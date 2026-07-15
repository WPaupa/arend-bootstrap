package monad;

import org.arend.ext.ArendExtension;
import org.arend.ext.DefinitionContributor;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.module.ModulePath;
import org.arend.ext.reference.MetaRef;
import org.arend.ext.reference.Precedence;
import org.arend.ext.typechecking.MetaDefinition;
import org.arend.ext.typechecking.MetaResolver;
import org.arend.ext.typechecking.meta.TrivialMetaTypechecker;
import org.jetbrains.annotations.NotNull;

import java.util.Collections;

import static org.arend.ext.prettyprinting.doc.DocFactory.multiline;

/**
 * The main extension class of the arend-bootstrap library. It declares the metas provided by the
 * library; currently only {@code do} (see {@link DoMeta}).
 */
@SuppressWarnings("unused")
public class MonadExtension implements ArendExtension {
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
        * a bind `\\lam x => a`, which binds the result of the monadic action `a` to `x` in the rest of the block (desugars to `a >>= \\lam x => rest`), or
        * a plain action `a`, whose result is discarded (desugars to `a >> rest`).

        For example, `do { \\lam a => ma, mb, \\lam c => mc a, return (a, c) }` is equivalent to
        `ma >>= \\lam a => mb >> (mc a >>= \\lam c => return (a, c))`.
        """), factory.metaDef(ref, Collections.emptyList(), null));
  }
}
