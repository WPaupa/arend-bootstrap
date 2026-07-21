package extensions;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteGoalExpression;
import org.arend.ext.concrete.expr.ConcreteHoleExpression;
import org.arend.ext.concrete.expr.ConcreteLamExpression;
import org.arend.ext.concrete.expr.ConcreteNumberExpression;
import org.arend.ext.concrete.expr.ConcretePiExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.concrete.expr.ConcreteSigmaExpression;
import org.arend.ext.concrete.expr.ConcreteStringExpression;
import org.arend.ext.concrete.expr.ConcreteTupleExpression;
import org.arend.ext.concrete.expr.ConcreteTypedExpression;
import org.arend.ext.concrete.expr.ConcreteUniverseExpression;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ContextDataChecker;
import org.arend.ext.typechecking.MetaResolver;
import org.arend.term.concrete.Concrete;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * {@code quot { E }} reifies the surface syntax of {@code E} into a value of the double-checker's
 * core AST {@code Expr} (see {@code ArendAST.Expression}). This class is the resolver half; the
 * builder half is {@link QuotBuild}.
 *
 * <p>This is a purely <b>syntactic</b> translation; {@code E} is never typechecked.
 * <ul>
 *   <li>A global variable is written {@code name$id} and becomes
 *       {@code EVar (GlobalVar name id EGoal nothingE)}; existence is not checked, so globals never
 *       fail.</li>
 *   <li>Any other name is a local; it must be bound by an enclosing {@code \lam}/{@code \Pi}/{@code \Sigma}
 *       in {@code E} (otherwise it is an error). Its {@code index} is its de Bruijn <b>level</b>
 *       (outermost binder = 0), matching how {@code ArendAST.Typecheck.Env.getLocal} resolves a local
 *       by index equality.</li>
 *   <li>Sorts cannot be recovered from surface syntax, so a default sort ({@code lp = 0},
 *       {@code lh = inf}) is used wherever one is required.</li>
 *   <li>A projection {@code e.n} becomes {@code EProj}; anything else without a readable accessor
 *       ({@code \let}, {@code \case}, {@code \new}, …) becomes {@code EGoal}.</li>
 * </ul>
 *
 * <p><b>Why two phases.</b> Reading names such as {@code foo$3} requires the resolve phase (they are
 * unresolved there), but the AST constructor references (bound via {@link org.arend.ext.typechecking.meta.Dependency})
 * are only populated in the typecheck phase. So the resolver walks {@code E} and emits a neutral,
 * reference-free encoding (nested tuples of numbers and strings — see the tag constants below), then
 * re-invokes {@code quot} on that encoding; {@link QuotBuild#invokeMeta} decodes it into {@code Expr}
 * using the (now populated) dependency references. This mirrors arend-lib's {@code ExistsResolver} /
 * {@code ExistsMeta} split.
 *
 * <p>Reading a projection {@code e.n} requires the internal {@code org.arend.term.concrete.Concrete}
 * node type (bundled in Arend.jar), since the public ext API exposes no projection accessor.
 */
public class QuotMeta implements MetaResolver {
  // Encoding tags. Nullary nodes (EUNIV, EGOAL) are encoded as a bare number; every other node is a
  // tuple whose first field is the tag. A list is a tuple of its element encodings.
  static final int EVAR = 0;
  static final int EAPP = 1;
  static final int ELAM = 2;
  static final int EPI = 3;
  static final int ESIGMA = 4;
  static final int ETUPLE = 5;
  static final int EUNIV = 6;
  static final int EINT = 7;
  static final int ESTRING = 8;
  static final int ETYPED = 9;
  static final int EGOAL = 10;
  static final int EPROJ = 11;
  static final int EPEVAL = 12;
  static final int EBOX = 13;
  static final int ELET = 14;
  static final int ECASE = 15;
  // List encoding markers (kept distinct from node tags). A list is a cons/nil chain rather than a
  // single tuple, because a one-element tuple `(x)` collapses to `x` in Arend concrete syntax.
  static final int NIL = 100;
  static final int CONS = 101;
  //   Level: LInfinity = a bare number; LMax = (LVL_MAX, varTag, offset, constant) with
  //   varTag 0 = nothing, 1 = LP, 2 = LH. A Sort is encoded as (lpLevel, lhLevel).
  static final int LVL_INF = 200;
  static final int LVL_MAX = 201;
  // Variant tags for encoded sub-structures. Each is decoded by a dedicated decoder, so the small
  // tag spaces below may overlap with one another and with the node tags above.
  //   MaybeExpr: nothing = a bare number; just = (JUST, enc).
  static final int JUST = 1;
  //   LetPattern: LPName = (LP_NAME, name, level); LPTuple = (LP_TUPLE, chain).
  static final int LP_NAME = 0;
  static final int LP_TUPLE = 1;
  //   Match: NoMatch = (NO_MATCH, enc); DoMatch = (DO_MATCH, chain of clauses).
  static final int NO_MATCH = 0;
  static final int DO_MATCH = 1;
  //   Pattern: PVar = (P_VAR, var); PConstr = (P_CONSTR, var, chain); PAbsurd = a bare number.
  static final int P_VAR = 0;
  static final int P_CONSTR = 1;
  static final int P_ABSURD = 2;

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!new ContextDataChecker().checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }
    ConcreteFactory factory = contextData.getFactory();
    if (contextData.getCoclauses() != null) {
      return factory.withData(contextData.getCoclauses().getData()).goal();
    }
    List<? extends ConcreteArgument> args = contextData.getArguments();
    if (args.size() != 1) {
      resolver.getErrorReporter().report(new NameResolverError("Expected a single expression to quote", contextData.getMarker()));
      return null;
    }
    ConcreteExpression code = new Encoder(factory, resolver).enc(args.getFirst().getExpression(), Ctx.EMPTY);
    if (code == null) {
      return null;
    }
    // Re-invoke `quot` on the neutral encoding; QuotBuild.invokeMeta decodes it at typecheck time.
    return factory.app(contextData.getReferenceExpression(), true, code);
  }

  // Immutable local context of binders, keyed by name (innermost first). The stored level is the
  // de Bruijn level (number of binders already in scope when this binder was introduced); `type` is
  // the binder's declared type encoding (or null if none), so every occurrence of a variable can be
  // given the same type.
  static final class Ctx {
    static final Ctx EMPTY = new Ctx(null, -1, null, null, 0);
    final String name;
    final int level;
    final ConcreteExpression type;
    final Ctx prev;
    final int size;

    private Ctx(String name, int level, ConcreteExpression type, Ctx prev, int size) {
      this.name = name;
      this.level = level;
      this.type = type;
      this.prev = prev;
      this.size = size;
    }

    Ctx push(String name, ConcreteExpression type) {
      return new Ctx(name, size, type, this, size + 1);
    }

    Ctx find(String name) {
      for (Ctx c = this; c != EMPTY; c = c.prev) {
        if (name.equals(c.name)) {
          return c;
        }
      }
      return null;
    }
  }

  static boolean isNat(String s) {
    if (s.isEmpty()) {
      return false;
    }
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c < '0' || c > '9') {
        return false;
      }
    }
    return true;
  }

  private static final class Encoder {
    private final ConcreteFactory factory;
    private final ExpressionResolver resolver;

    Encoder(ConcreteFactory factory, ExpressionResolver resolver) {
      this.factory = factory;
      this.resolver = resolver;
    }

    private ConcreteExpression tag(int t) {
      return factory.number(t);
    }

    private ConcreteExpression cons(ConcreteExpression head, ConcreteExpression tail) {
      return factory.tuple(List.of(tag(CONS), head, tail));
    }

    private ConcreteExpression listChain(List<ConcreteExpression> items) {
      ConcreteExpression acc = tag(NIL);
      for (int i = items.size() - 1; i >= 0; i--) {
        acc = cons(items.get(i), acc);
      }
      return acc;
    }

    // A reference variable: (isGlobal, name, id-or-level, typeEnc). Used inside EVar and in patterns.
    private ConcreteExpression encVar(boolean global, String name, ConcreteExpression key, ConcreteExpression type) {
      return factory.tuple(List.of(tag(global ? 1 : 0), factory.string(name), key, type));
    }

    // === sorts / levels ===
    // Analyze a level expression into {infFlag, varTag, offset, constant}, or null if too complex.
    private int @Nullable [] analyzeLevel(Concrete.LevelExpression le) {
      if (le instanceof Concrete.PLevelExpression) {
        return new int[] { 0, 1, 0, 0 };
      }
      if (le instanceof Concrete.HLevelExpression) {
        return new int[] { 0, 2, 0, 0 };
      }
      if (le instanceof Concrete.InfLevelExpression) {
        return new int[] { 1, 0, 0, 0 };
      }
      if (le instanceof Concrete.NumberLevelExpression n) {
        return new int[] { 0, 0, 0, n.getNumber() };
      }
      if (le instanceof Concrete.SucLevelExpression suc) {
        int[] a = analyzeLevel(suc.getExpression());
        if (a == null) {
          return null;
        }
        return a[0] == 1 ? a : new int[] { 0, a[1], a[2] + 1, a[3] + 1 };
      }
      // \max and named/inference level variables are not represented.
      return null;
    }

    private ConcreteExpression encLevelOf(int[] a) {
      return a[0] == 1 ? tag(LVL_INF) : factory.tuple(List.of(tag(LVL_MAX), tag(a[1]), factory.number(a[2]), factory.number(a[3])));
    }

    // A level in the p (predicative) or h (homotopy) position; the default is 0 for p and inf for h.
    private ConcreteExpression encLevel(@Nullable Concrete.LevelExpression le, boolean isH) {
      int[] a = le == null ? null : analyzeLevel(le);
      if (a == null) {
        a = isH ? new int[] { 1, 0, 0, 0 } : new int[] { 0, 0, 0, 0 };
      }
      return encLevelOf(a);
    }

    private ConcreteExpression defaultSortEnc() {
      return factory.tuple(List.of(encLevel(null, false), encLevel(null, true)));
    }

    private ConcreteExpression sortFromUniverse(Concrete.UniverseExpression u) {
      return factory.tuple(List.of(encLevel(u.getPLevel(), false), encLevel(u.getHLevel(), true)));
    }

    // The sort of a type-former: taken from an ascribed universe if there is one, else the default.
    private ConcreteExpression sortFromAscribed(@Nullable ConcreteExpression ascribed) {
      return ascribed instanceof Concrete.UniverseExpression u ? sortFromUniverse(u) : defaultSortEnc();
    }

    // Wrap `core` in ETyped when a type is ascribed but the node does not absorb it itself.
    private @Nullable ConcreteExpression ascribe(ConcreteExpression core, Ctx ctx, @Nullable ConcreteExpression ascribed) {
      if (ascribed == null) {
        return core;
      }
      ConcreteExpression t = enc(ascribed, ctx);
      return t == null ? null : factory.tuple(List.of(tag(ETYPED), core, t));
    }

    private @Nullable ConcreteExpression enc(ConcreteExpression e, Ctx ctx) {
      return enc(e, ctx, null);
    }

    // Returns null (after reporting an error) on a hard failure (an unbound local). `ascribed` is the
    // type from an enclosing `(e : ascribed)`; nodes with a type/sort slot absorb it, others wrap in
    // ETyped (see `ascribe`).
    private @Nullable ConcreteExpression enc(ConcreteExpression e, Ctx ctx, @Nullable ConcreteExpression ascribed) {
      // Application `f a_1 ... a_n` (at resolve time this is an unresolved sequence, not a
      // ConcreteAppExpression, so use the uniform argument-sequence accessor).
      List<? extends ConcreteArgument> seq = e.getArgumentsSequence();
      if (seq.size() > 1) {
        ConcreteExpression acc = enc(seq.get(0).getExpression(), ctx);
        if (acc == null) {
          return null;
        }
        for (int i = 1; i < seq.size(); i++) {
          ConcreteExpression ta = enc(seq.get(i).getExpression(), ctx);
          if (ta == null) {
            return null;
          }
          acc = factory.tuple(List.of(tag(EAPP), acc, ta, tag(seq.get(i).isExplicit() ? 1 : 0)));
        }
        return ascribe(acc, ctx, ascribed);
      }

      if (e instanceof ConcreteReferenceExpression r) {
        // A variable absorbs the ascribed type (as its VType); otherwise it takes the type recorded
        // for it at its binder, so every occurrence carries the same type.
        ConcreteExpression ascType = null;
        if (ascribed != null) {
          ascType = enc(ascribed, ctx);
          if (ascType == null) {
            return null;
          }
        }
        String name = r.getReferent().getRefName();
        int d = name.lastIndexOf('$');
        if (d >= 0 && isNat(name.substring(d + 1))) {
          ConcreteExpression t = ascType != null ? ascType : tag(EGOAL);
          return factory.tuple(List.of(tag(EVAR),
              encVar(true, name.substring(0, d), factory.number(new java.math.BigInteger(name.substring(d + 1))), t)));
        }
        Ctx entry = ctx.find(name);
        if (entry == null) {
          resolver.getErrorReporter().report(new NameResolverError("Unbound variable: " + name, r));
          return null;
        }
        ConcreteExpression t = ascType != null ? ascType : (entry.type != null ? entry.type : tag(EGOAL));
        return factory.tuple(List.of(tag(EVAR), encVar(false, name, factory.number(entry.level), t)));
      }

      if (e instanceof ConcreteNumberExpression n) {
        return ascribe(factory.tuple(List.of(tag(EINT), factory.number(n.getNumber()))), ctx, ascribed);
      }

      if (e instanceof ConcreteStringExpression s) {
        return ascribe(factory.tuple(List.of(tag(ESTRING), factory.string(s.getUnescapedString()))), ctx, ascribed);
      }

      // `(e : T)`: translate e with T as its ascribed type (which it absorbs, or wraps in ETyped).
      if (e instanceof ConcreteTypedExpression t) {
        ConcreteExpression inner = enc(t.getExpression(), ctx, t.getType());
        return inner == null ? null : ascribe(inner, ctx, ascribed);
      }

      // A tuple must carry its type; use the ascribed one instead of EGoal + an ETyped wrapper.
      if (e instanceof ConcreteTupleExpression tuple) {
        ConcreteExpression list = encList(tuple.getFields(), ctx);
        if (list == null) {
          return null;
        }
        ConcreteExpression type;
        if (ascribed == null) {
          type = tag(EGOAL);
        } else {
          type = enc(ascribed, ctx);
          if (type == null) {
            return null;
          }
        }
        return factory.tuple(List.of(tag(ETUPLE), list, type));
      }

      if (e instanceof ConcreteLamExpression lam) {
        ConcreteExpression core = binder(lam.getParameters(), lam.getBody(), ctx, ELAM, null);
        return core == null ? null : ascribe(core, ctx, ascribed);
      }
      if (e instanceof ConcretePiExpression pi) {
        return binder(pi.getParameters(), pi.getCodomain(), ctx, EPI, ascribed);
      }
      if (e instanceof ConcreteSigmaExpression sigma) {
        return binder(sigma.getParameters(), null, ctx, ESIGMA, ascribed);
      }

      // A universe's sort comes from its own levels, or an ascribed universe, else the default.
      if (e instanceof Concrete.UniverseExpression u) {
        ConcreteExpression sortEnc;
        if (u.getPLevel() != null || u.getHLevel() != null) {
          sortEnc = sortFromUniverse(u);
        } else if (ascribed instanceof Concrete.UniverseExpression au) {
          sortEnc = sortFromUniverse(au);
        } else {
          sortEnc = defaultSortEnc();
        }
        return factory.tuple(List.of(tag(EUNIV), sortEnc));
      }

      // Projection `e.n`. The ext API has no accessor for it, so we read the internal concrete node
      // (bundled in Arend.jar). `getField()` is 0-based, matching the core AST's `EProj` index.
      if (e instanceof Concrete.ProjExpression proj) {
        ConcreteExpression sub = enc(proj.getExpression(), ctx);
        // isProperty is not recoverable from surface syntax, so default to false (0).
        return sub == null ? null : ascribe(factory.tuple(List.of(tag(EPROJ), sub, factory.number(proj.getField()), tag(0))), ctx, ascribed);
      }

      // `\peval e` / `\eval e` -> EPEval (the AST has no non-`peval` variant).
      if (e instanceof Concrete.EvalExpression eval) {
        ConcreteExpression sub = enc(eval.getExpression(), ctx);
        return sub == null ? null : ascribe(factory.tuple(List.of(tag(EPEVAL), sub)), ctx, ascribed);
      }

      // `\box e` -> EBox e T (the value type is the ascribed one, or EGoal).
      if (e instanceof Concrete.BoxExpression box) {
        ConcreteExpression sub = enc(box.getExpression(), ctx);
        if (sub == null) {
          return null;
        }
        ConcreteExpression type;
        if (ascribed == null) {
          type = tag(EGOAL);
        } else {
          type = enc(ascribed, ctx);
          if (type == null) {
            return null;
          }
        }
        return factory.tuple(List.of(tag(EBOX), sub, type));
      }

      if (e instanceof Concrete.LetExpression let) {
        ConcreteExpression core = encLet(let, ctx);
        return core == null ? null : ascribe(core, ctx, ascribed);
      }
      if (e instanceof Concrete.CaseExpression caseExpr) {
        ConcreteExpression core = encCase(caseExpr, ctx);
        return core == null ? null : ascribe(core, ctx, ascribed);
      }

      // Goals, holes, and everything else without a readable accessor.
      return ascribe(tag(EGOAL), ctx, ascribed);
    }

    // MaybeExpr: nothing (null) -> a bare marker; just -> (JUST, enc).
    private @Nullable ConcreteExpression encMaybe(@Nullable ConcreteExpression e, Ctx ctx) {
      if (e == null) {
        return tag(NIL);
      }
      ConcreteExpression c = enc(e, ctx);
      return c == null ? null : factory.tuple(List.of(tag(JUST), c));
    }

    // ELet (isSFunc, Array LetClause, in). Arend `\let` is (mutually) recursive for scoping: every
    // clause body and the `in` body see all clause-bound names, so we assign all levels first, then
    // record each single-name clause's declared type so its occurrences share it.
    private @Nullable ConcreteExpression encLet(Concrete.LetExpression let, Ctx ctx) {
      ConcreteExpression isSFunc = tag(let.isStrict() ? 1 : 0);
      List<? extends Concrete.LetClause> clauses = let.getClauses();
      // Pass A: assign levels (types not known yet); this context is enough to encode the types.
      Ctx[] tmp = { ctx };
      List<ConcreteExpression> pats = new ArrayList<>();
      for (Concrete.LetClause clause : clauses) {
        pats.add(encLetPattern(clause.getPattern(), tmp));
      }
      Ctx levelCtx = tmp[0];
      // Pass B: rebuild the context (same names/levels), recording declared types.
      Ctx[] typed = { ctx };
      for (Concrete.LetClause clause : clauses) {
        ConcreteExpression tEnc = null;
        if (clause.getPattern() instanceof Concrete.NamePattern && clause.getResultType() != null) {
          tEnc = enc(clause.getResultType(), levelCtx);
          if (tEnc == null) {
            return null;
          }
        }
        pushLetBinders(clause.getPattern(), tEnc, typed);
      }
      Ctx bodyCtx = typed[0];
      // Pass C: encode clause bodies/types and the `in` body under the typed context.
      List<ConcreteExpression> clauseEncs = new ArrayList<>();
      for (int i = 0; i < clauses.size(); i++) {
        Concrete.LetClause clause = clauses.get(i);
        // Parameters of `\let f x => e` fold into a lambda body `\lam x => e`.
        ConcreteExpression body = clause.getParameters().isEmpty()
            ? enc(clause.getTerm(), bodyCtx)
            : binder(clause.getParameters(), clause.getTerm(), bodyCtx, ELAM, null);
        if (body == null) {
          return null;
        }
        ConcreteExpression type = encMaybe(clause.getResultType(), bodyCtx);
        if (type == null) {
          return null;
        }
        clauseEncs.add(factory.tuple(List.of(pats.get(i), body, type, isSFunc)));
      }
      ConcreteExpression bodyEnc = enc(let.getExpression(), bodyCtx);
      return bodyEnc == null ? null : factory.tuple(List.of(tag(ELET), isSFunc, listChain(clauseEncs), bodyEnc));
    }

    // A let pattern binds new locals; assign each a fresh de Bruijn level (mutating cur).
    private ConcreteExpression encLetPattern(Concrete.Pattern pat, Ctx[] cur) {
      if (pat instanceof Concrete.TuplePattern tp) {
        List<ConcreteExpression> subs = new ArrayList<>();
        for (Concrete.Pattern sp : tp.getPatterns()) {
          subs.add(encLetPattern(sp, cur));
        }
        return factory.tuple(List.of(tag(LP_TUPLE), listChain(subs)));
      }
      String name = pat instanceof Concrete.NamePattern np && np.getRef() != null ? np.getRef().getRefName() : "_";
      int level = cur[0].size;
      cur[0] = cur[0].push(name, null);
      return factory.tuple(List.of(tag(LP_NAME), factory.string(name), factory.number(level)));
    }

    // Re-push a let pattern's binders (same order/levels as encLetPattern), giving a single
    // NamePattern the supplied type so its uses carry it.
    private void pushLetBinders(Concrete.Pattern pat, @Nullable ConcreteExpression type, Ctx[] cur) {
      if (pat instanceof Concrete.TuplePattern tp) {
        for (Concrete.Pattern sp : tp.getPatterns()) {
          pushLetBinders(sp, null, cur);
        }
        return;
      }
      String name = pat instanceof Concrete.NamePattern np && np.getRef() != null ? np.getRef().getRefName() : "_";
      cur[0] = cur[0].push(name, type);
    }

    // ECase (isSFunc, Array Var params, returnType, returnLevel, Match, Array Expr args).
    private @Nullable ConcreteExpression encCase(Concrete.CaseExpression caseExpr, Ctx ctx) {
      // Scrutinees are in the outer scope.
      List<ConcreteExpression> argEncs = new ArrayList<>();
      for (Concrete.CaseArgument ca : caseExpr.getArguments()) {
        ConcreteExpression a = enc(ca.expression, ctx);
        if (a == null) {
          return null;
        }
        argEncs.add(a);
      }
      // The \as-binders (one per scrutinee) are in scope for the return type only.
      Ctx cur = ctx;
      List<ConcreteExpression> paramEncs = new ArrayList<>();
      for (Concrete.CaseArgument ca : caseExpr.getArguments()) {
        String nm = ca.referable != null ? ca.referable.getRefName() : "_";
        int level = cur.size;
        ConcreteExpression vt;
        if (ca.type == null) {
          vt = tag(EGOAL);
        } else {
          vt = enc(ca.type, cur);
          if (vt == null) {
            return null;
          }
        }
        paramEncs.add(factory.tuple(List.of(factory.string(nm), factory.number(level), vt)));
        cur = cur.push(nm, ca.type == null ? null : vt);
      }
      ConcreteExpression retType = caseExpr.getResultType() == null ? tag(EGOAL) : enc(caseExpr.getResultType(), cur);
      if (retType == null) {
        return null;
      }
      ConcreteExpression retLevel = encMaybe(caseExpr.getResultTypeLevel(), cur);
      if (retLevel == null) {
        return null;
      }
      // Clauses bind their own pattern variables (in the outer scope, not under the \as-binders).
      List<ConcreteExpression> clauseEncs = new ArrayList<>();
      for (Concrete.FunctionClause fc : caseExpr.getClauses()) {
        ConcreteExpression c = encCaseClause(fc, ctx);
        if (c == null) {
          return null;
        }
        clauseEncs.add(c);
      }
      ConcreteExpression match = factory.tuple(List.of(tag(DO_MATCH), listChain(clauseEncs)));
      return factory.tuple(List.of(tag(ECASE), tag(caseExpr.isSCase() ? 1 : 0), listChain(paramEncs),
          retType, retLevel, match, listChain(argEncs)));
    }

    // A case clause: cClause (Array Pattern, MaybeExpr body). Pattern variables bind locals for the body.
    private @Nullable ConcreteExpression encCaseClause(Concrete.FunctionClause fc, Ctx ctx) {
      Ctx[] cur = { ctx };
      List<ConcreteExpression> patEncs = new ArrayList<>();
      for (Concrete.Pattern p : fc.getPatterns()) {
        patEncs.add(encPattern(p, cur));
      }
      ConcreteExpression body = encMaybe(fc.getExpression(), cur[0]);
      return body == null ? null : factory.tuple(List.of(listChain(patEncs), body));
    }

    // A case pattern. A `name$id` name-pattern is a nullary constructor; a plain name binds a local.
    // Constructor patterns' arguments bind further locals. Unreadable/unsupported patterns -> PAbsurd.
    private ConcreteExpression encPattern(Concrete.Pattern pat, Ctx[] cur) {
      if (pat instanceof Concrete.NamePattern np) {
        String name = np.getRef() != null ? np.getRef().getRefName() : "_";
        int d = name.lastIndexOf('$');
        if (d >= 0 && isNat(name.substring(d + 1))) {
          ConcreteExpression v = encVar(true, name.substring(0, d), factory.number(new java.math.BigInteger(name.substring(d + 1))), tag(EGOAL));
          return factory.tuple(List.of(tag(P_CONSTR), v, tag(NIL)));
        }
        int level = cur[0].size;
        cur[0] = cur[0].push(name, null);
        return factory.tuple(List.of(tag(P_VAR), encVar(false, name, factory.number(level), tag(EGOAL))));
      }
      if (pat instanceof Concrete.ConstructorPattern cp) {
        return encConstrPattern(cp.getConstructor(), cp.getPatterns(), cur);
      }
      // At resolve time a constructor application `con a b` is still an unparsed binop sequence.
      // Handle the prefix form (first element = constructor, rest = argument patterns).
      if (pat instanceof Concrete.UnparsedConstructorPattern up) {
        List<? extends Concrete.BinOpSequenceElem<Concrete.Pattern>> elems = up.getUnparsedPatterns();
        if (elems.size() == 1) {
          return encPattern(elems.get(0).getComponent(), cur);
        }
        List<Concrete.Pattern> args = new ArrayList<>();
        for (int i = 1; i < elems.size(); i++) {
          args.add(elems.get(i).getComponent());
        }
        Concrete.Pattern head = elems.get(0).getComponent();
        org.arend.ext.reference.ArendRef ctor = head instanceof Concrete.NamePattern hnp ? hnp.getRef() : null;
        return encConstrPattern(ctor, args, cur);
      }
      // Absurd `()`, number patterns, and other unreadable patterns have no faithful representation.
      return tag(P_ABSURD);
    }

    private ConcreteExpression encConstrPattern(@Nullable ArendRef ctor, List<? extends Concrete.Pattern> argPats, Ctx[] cur) {
      String name = ctor != null ? ctor.getRefName() : "_";
      int d = name.lastIndexOf('$');
      String cn = d >= 0 ? name.substring(0, d) : name;
      java.math.BigInteger id = d >= 0 && isNat(name.substring(d + 1)) ? new java.math.BigInteger(name.substring(d + 1)) : java.math.BigInteger.ZERO;
      List<ConcreteExpression> subs = new ArrayList<>();
      for (Concrete.Pattern sp : argPats) {
        subs.add(encPattern(sp, cur));
      }
      return factory.tuple(List.of(tag(P_CONSTR), encVar(true, cn, factory.number(id), tag(EGOAL)), listChain(subs)));
    }

    private @Nullable ConcreteExpression encList(List<? extends ConcreteExpression> es, Ctx ctx) {
      ConcreteExpression acc = tag(NIL);
      for (int i = es.size() - 1; i >= 0; i--) {
        ConcreteExpression c = enc(es.get(i), ctx);
        if (c == null) {
          return null;
        }
        acc = cons(c, acc);
      }
      return acc;
    }

    private @Nullable ConcreteExpression binder(List<? extends ConcreteParameter> params, @Nullable ConcreteExpression body, Ctx ctx, int kind, @Nullable ConcreteExpression ascribed) {
      Ctx cur = ctx;
      List<ConcreteExpression> tele = new ArrayList<>();
      for (ConcreteParameter p : params) {
        ConcreteExpression typeC = p.getType();
        for (ArendRef pr : p.getRefList()) {
          String nm = pr == null ? "_" : pr.getRefName();
          int level = cur.size;
          ConcreteExpression typeEnc;
          if (typeC == null) {
            typeEnc = tag(EGOAL);
          } else {
            typeEnc = enc(typeC, cur);
            if (typeEnc == null) {
              return null;
            }
          }
          tele.add(factory.tuple(List.of(factory.string(nm), factory.number(level), typeEnc)));
          // Record the declared type so every use of this variable is given the same type.
          cur = cur.push(nm, typeC == null ? null : typeEnc);
        }
      }
      ConcreteExpression teleList = listChain(tele);
      // A lambda's result sort is not recoverable from surface syntax; a \Pi/\Sigma sort may be given
      // by an ascribed universe.
      ConcreteExpression sortEnc = kind == ELAM ? defaultSortEnc() : sortFromAscribed(ascribed);
      if (kind == ESIGMA) {
        return factory.tuple(List.of(tag(ESIGMA), teleList, sortEnc));
      }
      ConcreteExpression b = enc(body, cur);
      return b == null ? null : factory.tuple(List.of(tag(kind), teleList, b, sortEnc));
    }
  }
}
