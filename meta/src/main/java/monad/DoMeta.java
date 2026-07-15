package monad;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteIncompleteExpression;
import org.arend.ext.concrete.expr.ConcreteLamExpression;
import org.arend.ext.concrete.expr.ConcreteTupleExpression;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.NameResolverError;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.module.LongName;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.reference.ExpressionResolver;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.MetaResolver;
import org.arend.ext.typechecking.TypedExpression;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collections;
import java.util.List;

/**
 * Do-notation for monads (see {@code Utilities.Monad}).
 *
 * <p>{@code do { s_1, ... s_n }} desugars a sequence of monadic statements into a chain of
 * {@code >>=} and {@code >>}. The last statement is the result of the block; each preceding
 * statement is either
 * <ul>
 *   <li>a <b>bind</b>, written as a lambda {@code \lam x => a}, which binds the result of the
 *       monadic action {@code a} to {@code x} in the rest of the block, i.e. it is desugared to
 *       {@code a >>= \lam x => rest}; or</li>
 *   <li>a plain monadic action {@code a}, whose result is discarded, i.e. it is desugared to
 *       {@code a >> rest}.</li>
 * </ul>
 *
 * <p>For example,
 * <pre>
 * do {
 *   \lam a => ma,
 *   mb,
 *   \lam c => mc a,
 *   return (a, c)
 * }
 * </pre>
 * is equivalent to {@code ma >>= \lam a => mb >> (mc a >>= \lam c => return (a, c))}.
 *
 * <p>The operators {@code >>=} and {@code >>} are referenced by name and resolved at the call
 * site, so this meta works for any monad that provides them (e.g. any instance of
 * {@code Utilities.Monad.Monad}).
 */
public class DoMeta extends BaseMetaDefinition implements MetaResolver {
  @Override
  public boolean @Nullable [] argumentExplicitness() {
    return new boolean[] { false };
  }

  @Override
  public boolean allowEmptyCoclauses() {
    return true;
  }

  // A comma-separated list of statements is parsed as a tuple; a single statement is not.
  private static List<? extends ConcreteExpression> getStatements(ConcreteExpression expr) {
    return expr instanceof ConcreteTupleExpression tuple ? tuple.getFields() : Collections.singletonList(expr);
  }

  private @Nullable ConcreteExpression getConcreteRepresentation(@NotNull ContextData contextData, @NotNull ErrorReporter errorReporter) {
    ConcreteFactory factory = contextData.getFactory();
    List<? extends ConcreteExpression> stmts = getStatements(contextData.getArguments().getFirst().getExpression());
    if (stmts.isEmpty()) {
      errorReporter.report(new NameResolverError("Expected at least one statement in the do block", contextData.getMarker()));
      return null;
    }

    ConcreteExpression result = stmts.getLast();
    for (int i = stmts.size() - 2; i >= 0; i--) {
      ConcreteExpression stmt = stmts.get(i);
      ConcreteFactory stmtFactory = factory.withData(stmt.getData());
      if (stmt instanceof ConcreteLamExpression lam && !(lam.getBody() instanceof ConcreteIncompleteExpression)) {
        // `\lam x => a` binds the result of `a` to `x` in the rest of the block: `a >>= \lam x => rest`.
        ArendRef bind = stmtFactory.unresolved(new LongName(">>="));
        ConcreteExpression continuation = stmtFactory.lam(lam.getParameters(), result);
        result = stmtFactory.app(stmtFactory.ref(bind), true, lam.getBody(), continuation);
      } else {
        // A plain action `a` sequences without binding: `a >> rest`.
        ArendRef then = stmtFactory.unresolved(new LongName(">>"));
        result = stmtFactory.app(stmtFactory.ref(then), true, stmt, result);
      }
    }
    return result;
  }

  @Override
  public @Nullable ConcreteExpression resolvePrefix(@NotNull ExpressionResolver resolver, @NotNull ContextData contextData) {
    if (!checkContextData(contextData, resolver.getErrorReporter())) {
      return null;
    }
    if (contextData.getArguments().isEmpty() == (contextData.getCoclauses() == null)) {
      resolver.getErrorReporter().report(new NameResolverError("Expected 1 implicit argument", contextData.getMarker()));
      return null;
    }
    if (contextData.getCoclauses() != null) {
      return contextData.getFactory().withData(contextData.getCoclauses().getData()).goal();
    }

    ConcreteExpression representation = getConcreteRepresentation(contextData, resolver.getErrorReporter());
    return representation == null ? null : resolver.resolve(representation);
  }

  @Override
  public @Nullable TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
    // `do` is a purely syntactic macro that is fully expanded during name resolution (see
    // resolvePrefix). It cannot be invoked directly by the typechecker because it emits references
    // to `>>=` and `>>` that must be resolved in the caller's scope.
    typechecker.getErrorReporter().report(new TypecheckingError("`do` can only be used in a position where it is resolved", contextData.getMarker()));
    return null;
  }
}
