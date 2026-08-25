package extensions;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteNumberExpression;
import org.arend.ext.concrete.expr.ConcreteTupleExpression;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.typechecking.meta.Dependency;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * The typecheck-phase half of {@code quot} (see {@link QuotMeta}). Its {@code invokeMeta} receives
 * the neutral encoding produced by {@link QuotMeta}'s resolver and decodes it into an {@code Expr}
 * value, using the AST constructor references bound via {@link Dependency}. Dependency fields are
 * populated (by {@code DependencyMetaTypechecker}) before {@code invokeMeta} runs, which is why the
 * construction happens here rather than in the resolver.
 */
public class QuotBuild extends BaseMetaDefinition {
  // Expr constructors
  @Dependency ArendRef EVar;
  @Dependency ArendRef EApp;
  @Dependency ArendRef ELam;
  @Dependency ArendRef EPiType;
  @Dependency ArendRef ESigmaType;
  @Dependency ArendRef ETuple;
  @Dependency ArendRef EProj;
  @Dependency ArendRef EUniv;
  @Dependency ArendRef EInt;
  @Dependency ArendRef EString;
  @Dependency ArendRef ETyped;
  @Dependency ArendRef EGoal;
  @Dependency ArendRef EPEval;
  @Dependency ArendRef EBox;
  @Dependency ArendRef ELet;
  @Dependency ArendRef ECase;
  @Dependency ArendRef ETInt;
  @Dependency ArendRef ETString;
  @Dependency ArendRef ENat;
  @Dependency ArendRef ETNat;
  @Dependency ArendRef EFin;
  @Dependency ArendRef ETFin;
  // Constructor expressions
  @Dependency ArendRef ECSuc;
  @Dependency ArendRef ECPos;
  @Dependency ArendRef ECNeg;
  // Var constructors
  @Dependency ArendRef GlobalVar;
  @Dependency ArendRef LocalVar;
  // Maybe Expr (Data.Maybe)
  @Dependency ArendRef nothing;
  @Dependency ArendRef just;
  // let clauses / patterns
  @Dependency ArendRef cLetClause;
  @Dependency ArendRef LPName;
  @Dependency ArendRef LPTuple;
  // match / clauses / patterns
  @Dependency ArendRef NoMatch;
  @Dependency ArendRef DoMatch;
  @Dependency ArendRef cClause;
  @Dependency ArendRef PVar;
  @Dependency ArendRef PConstr;
  @Dependency ArendRef PAbsurd;
  @Dependency ArendRef PZero;
  @Dependency ArendRef PSuc;
  @Dependency ArendRef PPos;
  @Dependency ArendRef PNeg;
  // Sort / levels (Arend 1.12: PLevel / HLevel)
  @Dependency ArendRef Sort;
  @Dependency(name = "Sort.lp") ArendRef lp;
  @Dependency(name = "Sort.lh") ArendRef lh;
  @Dependency ArendRef PLConst;
  @Dependency ArendRef PLVar;
  @Dependency ArendRef PLSuc;
  @Dependency ArendRef PLMax;
  @Dependency ArendRef PLInf;
  @Dependency ArendRef HLFin;
  @Dependency ArendRef HLInf;
  // stdlib
  @Dependency(name = "true") ArendRef trueRef;
  @Dependency(name = "false") ArendRef falseRef;

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    ConcreteExpression code = contextData.getArguments().getFirst().getExpression();
    ConcreteExpression built = new Decoder(contextData.getFactory()).dec(code);
    return typechecker.typecheck(built, contextData.getExpectedType());
  }

  private final class Decoder {
    private final ConcreteFactory factory;

    Decoder(ConcreteFactory factory) {
      this.factory = factory;
    }

    private ConcreteExpression con(ArendRef ctor, ConcreteExpression... args) {
      ConcreteExpression head = factory.ref(ctor);
      return args.length == 0 ? head : factory.app(head, true, args);
    }

    // A Sort is encoded as (pLevel, hLevel); build `\new Sort { | lp => .. | lh => .. }`.
    private ConcreteExpression decSort(ConcreteExpression e) {
      List<? extends ConcreteExpression> fs = ((ConcreteTupleExpression) e).getFields();
      return factory.newExpr(factory.classExt(factory.ref(Sort),
          factory.implementation(lp, decPLevel(fs.get(0))),
          factory.implementation(lh, decHLevel(fs.get(1)))));
    }

    // A p-level tuple -> the matching PLevel constructor.
    private ConcreteExpression decPLevel(ConcreteExpression e) {
      if (!(e instanceof ConcreteTupleExpression t)) {
        return con(PLInf);
      }
      List<? extends ConcreteExpression> fs = t.getFields();
      return switch (intOf(fs.get(0))) {
        case QuotMeta.PL_CONST -> con(PLConst, fs.get(1));
        case QuotMeta.PL_VAR -> con(PLVar, fs.get(1));
        case QuotMeta.PL_SUC -> con(PLSuc, decPLevel(fs.get(1)));
        case QuotMeta.PL_MAX -> con(PLMax, decPLevel(fs.get(1)), decPLevel(fs.get(2)));
        default -> con(PLInf);
      };
    }

    // An h-level: (HL_FIN, int) -> HLFin int; a bare number -> HLInf.
    private ConcreteExpression decHLevel(ConcreteExpression e) {
      if (e instanceof ConcreteTupleExpression t) {
        return con(HLFin, t.getFields().get(1));
      }
      return con(HLInf);
    }

    // A chain of p-level encodings -> an Array PLevel.
    private ConcreteExpression decPLevelList(ConcreteExpression e) {
      List<ConcreteExpression> out = new ArrayList<>();
      for (ConcreteExpression c : chain(e)) {
        out.add(decPLevel(c));
      }
      return arr(out);
    }

    private int intOf(ConcreteExpression e) {
      return ((ConcreteNumberExpression) e).getNumber().intValueExact();
    }

    private ConcreteExpression arr(List<ConcreteExpression> xs) {
      ConcreteExpression acc = factory.ref(factory.getPrelude().getEmptyArrayRef());
      for (int i = xs.size() - 1; i >= 0; i--) {
        acc = factory.appBuilder(factory.ref(factory.getPrelude().getArrayConsRef())).app(xs.get(i)).app(acc).build();
      }
      return acc;
    }

    private ConcreteExpression dec(ConcreteExpression e) {
      // Nullary nodes are encoded as a bare number.
      if (!(e instanceof ConcreteTupleExpression t)) {
        return con(EGoal);
      }
      List<? extends ConcreteExpression> fs = t.getFields();
      int tag = intOf(fs.get(0));
      switch (tag) {
        case QuotMeta.EVAR -> {
          return con(EVar, decVar(fs.get(1)));
        }
        case QuotMeta.EAPP -> {
          return con(EApp, dec(fs.get(1)), dec(fs.get(2)), factory.ref(intOf(fs.get(3)) == 1 ? trueRef : falseRef));
        }
        case QuotMeta.ELAM -> {
          return con(ELam, decTele(fs.get(1)), dec(fs.get(2)), decSort(fs.get(3)));
        }
        case QuotMeta.EPI -> {
          return con(EPiType, decTele(fs.get(1)), dec(fs.get(2)), decSort(fs.get(3)));
        }
        case QuotMeta.ESIGMA -> {
          return con(ESigmaType, decTele(fs.get(1)), decSort(fs.get(2)));
        }
        case QuotMeta.EUNIV -> {
          return con(EUniv, decSort(fs.get(1)));
        }
        case QuotMeta.ETUPLE -> {
          return con(ETuple, decList(fs.get(1)), dec(fs.get(2)));
        }
        case QuotMeta.EPROJ -> {
          return con(EProj, dec(fs.get(1)), fs.get(2), factory.ref(intOf(fs.get(3)) == 1 ? trueRef : falseRef));
        }
        case QuotMeta.EINT -> {
          return con(EInt, fs.get(1));
        }
        case QuotMeta.ENAT -> {
          return con(ENat, fs.get(1));
        }
        case QuotMeta.ESTRING -> {
          return con(EString, fs.get(1));
        }
        case QuotMeta.ETYPED -> {
          return con(ETyped, dec(fs.get(1)), dec(fs.get(2)));
        }
        case QuotMeta.EPEVAL -> {
          return con(EPEval, dec(fs.get(1)));
        }
        case QuotMeta.EBOX -> {
          return con(EBox, dec(fs.get(1)), dec(fs.get(2)));
        }
        case QuotMeta.ELET -> {
          ConcreteExpression isSFunc = factory.ref(intOf(fs.get(1)) == 1 ? trueRef : falseRef);
          List<ConcreteExpression> clauses = new ArrayList<>();
          for (ConcreteExpression c : chain(fs.get(2))) {
            List<? extends ConcreteExpression> cf = ((ConcreteTupleExpression) c).getFields();
            // (letPattern, body, typeMaybe, isSFunc)
            clauses.add(con(cLetClause, decLetPattern(cf.get(0)), dec(cf.get(1)), decMaybe(cf.get(2)),
                factory.ref(intOf(cf.get(3)) == 1 ? trueRef : falseRef)));
          }
          return con(ELet, isSFunc, arr(clauses), dec(fs.get(3)));
        }
        case QuotMeta.ECASE -> {
          // (isSFunc, params, returnType, returnLevel, match, args)
          return con(ECase, factory.ref(intOf(fs.get(1)) == 1 ? trueRef : falseRef), decTele(fs.get(2)),
              dec(fs.get(3)), decPLevelList(fs.get(4)), decMatch(fs.get(5)), decList(fs.get(6)));
        }
        case QuotMeta.ECSUC -> {
          return con(ECSuc, dec(fs.get(1)));
        }
        case QuotMeta.ECPOS -> {
          return con(ECPos, dec(fs.get(1)));
        }
        case QuotMeta.ECNEG -> {
          return con(ECNeg, dec(fs.get(1)));
        }
        case QuotMeta.ETINT -> {
          return con(ETInt);
        }
        case QuotMeta.ETNAT -> {
          return con(ETNat);
        }
        case QuotMeta.EFIN -> {
          return con(EFin, dec(fs.get(1)), dec(fs.get(2)));
        }
        case QuotMeta.ETFIN -> {
          return con(ETFin, dec(fs.get(1)));
        }
        case QuotMeta.ETSTRING -> {
          return con(ETString);
        }
        default -> {
          return con(EGoal);
        }
      }
    }

    // A reference variable tuple (isGlobal, name, id-or-level, typeEnc) -> GlobalVar/LocalVar.
    private ConcreteExpression decVar(ConcreteExpression e) {
      List<? extends ConcreteExpression> fs = ((ConcreteTupleExpression) e).getFields();
      boolean global = intOf(fs.get(0)) == 1;
      return con(global ? GlobalVar : LocalVar, fs.get(1), fs.get(2), dec(fs.get(3)), con(nothing));
    }

    // Maybe Expr: a bare number -> nothing; (JUST, enc) -> just enc.
    private ConcreteExpression decMaybe(ConcreteExpression e) {
      if (e instanceof ConcreteTupleExpression t) {
        return con(just, dec(t.getFields().get(1)));
      }
      return con(nothing);
    }

    private ConcreteExpression decLetPattern(ConcreteExpression e) {
      List<? extends ConcreteExpression> fs = ((ConcreteTupleExpression) e).getFields();
      if (intOf(fs.get(0)) == QuotMeta.LP_TUPLE) {
        List<ConcreteExpression> subs = new ArrayList<>();
        for (ConcreteExpression sp : chain(fs.get(1))) {
          subs.add(decLetPattern(sp));
        }
        return con(LPTuple, arr(subs));
      }
      return con(LPName, fs.get(1), fs.get(2));
    }

    private ConcreteExpression decMatch(ConcreteExpression e) {
      List<? extends ConcreteExpression> fs = ((ConcreteTupleExpression) e).getFields();
      if (intOf(fs.get(0)) == QuotMeta.NO_MATCH) {
        return con(NoMatch, dec(fs.get(1)));
      }
      List<ConcreteExpression> clauses = new ArrayList<>();
      for (ConcreteExpression c : chain(fs.get(1))) {
        List<? extends ConcreteExpression> cf = ((ConcreteTupleExpression) c).getFields();
        // (patterns, bodyMaybe)
        List<ConcreteExpression> pats = new ArrayList<>();
        for (ConcreteExpression p : chain(cf.get(0))) {
          pats.add(decPattern(p));
        }
        clauses.add(con(cClause, arr(pats), decMaybe(cf.get(1))));
      }
      return con(DoMatch, arr(clauses));
    }

    private ConcreteExpression decPattern(ConcreteExpression e) {
      if (!(e instanceof ConcreteTupleExpression t)) {
        return con(PAbsurd);
      }
      List<? extends ConcreteExpression> fs = t.getFields();
      int tag = intOf(fs.get(0));
      switch (tag) {
        case QuotMeta.P_VAR -> {
          return con(PVar, decVar(fs.get(1)));
        }
        case QuotMeta.P_ZERO -> {
          return con(PZero);
        }
        case QuotMeta.P_SUC -> {
          return con(PSuc, decPattern(fs.get(1)));
        }
        case QuotMeta.P_POS -> {
          return con(PPos, decPattern(fs.get(1)));
        }
        case QuotMeta.P_NEG -> {
          return con(PNeg, decPattern(fs.get(1)));
        }
      }
      // P_CONSTR
      List<ConcreteExpression> subs = new ArrayList<>();
      for (ConcreteExpression sp : chain(fs.get(2))) {
        subs.add(decPattern(sp));
      }
      return con(PConstr, decVar(fs.get(1)), arr(subs));
    }

    // Walk a cons/nil chain (cons = (CONS, head, tail); nil = a bare number) into the element list.
    private List<ConcreteExpression> chain(ConcreteExpression e) {
      List<ConcreteExpression> out = new ArrayList<>();
      while (e instanceof ConcreteTupleExpression t) {
        List<? extends ConcreteExpression> fs = t.getFields();
        out.add(fs.get(1));
        e = fs.get(2);
      }
      return out;
    }

    private ConcreteExpression decList(ConcreteExpression e) {
      List<ConcreteExpression> out = new ArrayList<>();
      for (ConcreteExpression c : chain(e)) {
        out.add(dec(c));
      }
      return arr(out);
    }

    // A telescope is a chain of entries; each entry is a tuple (name, level, typeEncoding).
    private ConcreteExpression decTele(ConcreteExpression e) {
      List<ConcreteExpression> out = new ArrayList<>();
      for (ConcreteExpression entry : chain(e)) {
        List<? extends ConcreteExpression> ef = ((ConcreteTupleExpression) entry).getFields();
        out.add(con(LocalVar, ef.get(0), ef.get(1), dec(ef.get(2)), con(nothing)));
      }
      return arr(out);
    }
  }
}
