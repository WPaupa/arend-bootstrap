package extensions;

import org.arend.ext.ArendExtension;
import org.arend.ext.DefinitionContributor;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.module.ModulePath;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.MetaResolver;
import org.arend.ext.typechecking.meta.DependencyMetaTypechecker;
import org.arend.ext.typechecking.meta.TrivialMetaTypechecker;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;

import static org.arend.ext.prettyprinting.doc.DocFactory.multiline;
import static org.arend.ext.prettyprinting.doc.DocFactory.text;

/**
 * The main extension class of the arend-bootstrap library. It declares the metas provided by the
 * library: {@code do} (see {@link DoMeta}) and {@code quot} (see {@link QuotMeta}).
 */
@SuppressWarnings("unused")
public class StdExtension implements ArendExtension {
  private ConcreteFactory factory;

  @Override
  public void setConcreteFactory(@NotNull ConcreteFactory factory) {
    this.factory = factory;
  }

  @Override
  public void declareDefinitions(@NotNull DefinitionContributor contributor) {
    ModulePath module = new ModulePath("Monad", "Do");
    MetaDefinition doMeta = new DoMeta();
    MetaRef ref = factory.metaRef(factory.moduleRef(module), "do", Precedence.DEFAULT, null, null,
        (MetaResolver) doMeta, new TrivialMetaTypechecker(doMeta));
    contributor.declare(multiline("""
        `do { s_1, ... s_n }` is do-notation for monads (see `Utilities.Monad`).

        The last statement is the result of the block. Each preceding statement is either
        * a bind `\\lam x => a`, which binds the result of the monadic action `a` to `x` in the rest of the block (desugars to `a >>= \\lam x => rest`),
        * a pure let-binding `\\let b => e` (with no `\\in` body), which binds `b` to the non-monadic value `e` in the rest of the block (desugars to `\\let b => e \\in rest`), or
        * a plain action `a`, whose result is discarded (desugars to `a >> rest`).

        For example, `do { \\lam a => ma, \\let b => f a, \\lam c => mc b, return (a, c) }` is equivalent to
        `ma >>= \\lam a => \\let b => f a \\in (mc b >>= \\lam c => return (a, c))`.
        """), factory.metaDef(ref, Collections.emptyList(), null));

    // `quot { E }` reifies the surface syntax of E into the core AST `Expr` (ArendAST.Expression).
    // Its AST-constructor references are bound via @Dependency, resolved in this meta module's own
    // scope, so the modules below are imported into it (callers need not import anything).
    ModulePath quoteModule = new ModulePath("ArendAST", "Quote");
    contributor.declare(quoteModule, new ModulePath("ArendAST", "Expression"));
    contributor.declare(quoteModule, new ModulePath("ArendAST", "Level"));
    contributor.declare(quoteModule, new ModulePath("Data", "Bool"));
    contributor.declare(quoteModule, new ModulePath("Data", "Maybe"));
    QuotBuild quotBuild = new QuotBuild();
    DependencyMetaTypechecker quotTypechecker = new DependencyMetaTypechecker(QuotBuild.class, () -> quotBuild);
    MetaRef quotRef = factory.metaRef(factory.moduleRef(quoteModule), "quot", Precedence.DEFAULT, null, null,
        new QuotMeta(), quotTypechecker);
    contributor.declare(multiline("""
        `quot { E }` reifies the surface syntax of `E` into a value of the core AST `Expr` (see `ArendAST.Expression`).

        This is a purely syntactic translation; `E` is not typechecked.
        * A global variable is written `name$id` and becomes `EVar (GlobalVar name id EGoal nothingE)`; its existence is not checked.
        * Any other name is a local and must be bound by an enclosing `\\lam`/`\\Pi`/`\\Sigma` in `E`, otherwise it is an error. Its `index` is its de Bruijn level (outermost binder = 0).
        * A default sort (`lp = 0`, `lh = inf`) is used wherever a sort is required (surface syntax carries none).
        * Subexpressions with no readable representation (`\\let`, `\\case`, `\\new`, ...) become `EGoal`.
        """), factory.metaDef(quotRef, Collections.emptyList(), quotTypechecker.makeBody(factory)));
  }
}
