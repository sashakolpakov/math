import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-! # Injective Chain Dual -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual

noncomputable section

/-!
# Exact duality for simplicial cochains with injective coefficients

The actual cochain complex, after forgetting its scalar structure, is
naturally isomorphic to the additive Hom complex of the scalar chain complex.
The isomorphism is the already established simplex-evaluation duality, including
its compatibility with the boundary. Thus the exactness of Hom into an
injective module carries actual chain quasi-isomorphisms to cochain
quasi-isomorphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- The underlying additive-group complex of actual simplicial cochains. -/
abbrev additiveSimplicialCochains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  ((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (Singular.Basic.simplicialCochains K M)

/-- The additive Hom complex of the actual scalar simplicial chains. -/
abbrev additiveDualSimplicialChains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  ((preadditiveYoneda.obj M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (ChainDual.simplicialScalarChains (R := R) K).op

/-- Actual cochains are the Hom complex of actual chains, including the differential. -/
def simplicialCochainDualIso (K : SSet.{0}) (M : ModuleCat.{0} R) :
    additiveSimplicialCochains K M ≅ additiveDualSimplicialChains K M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((ChainDual.degreewiseChainDualEquiv K M n).toAddEquiv.trans
      ModuleCat.homAddEquiv.symm).toAddCommGrpIso)
    (by
      intro i j _
      apply AddCommGrpCat.ext
      intro c
      apply ModuleCat.hom_ext
      change (ChainDual.degreewiseChainDualEquiv K M i c).comp
          ((ChainDual.simplicialScalarChains (R := R) K).d j i).hom =
        ChainDual.degreewiseChainDualEquiv K M j ((Singular.Basic.simplicialCochains K M).d i j c)
      exact (ChainDual.degreewiseChainDualEquiv_d K M i j c).symm)

/-- The cochain-Hom comparison is natural for the actual simplicial pullback. -/
@[reassoc]
theorem simplicialCochainDualIso_naturality (M : ModuleCat.{0} R)
    {K L : SSet.{0}} (f : K ⟶ L) :
    ((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (Singular.Functor.simplicialPullback M f) ≫
        (simplicialCochainDualIso K M).hom =
      (simplicialCochainDualIso L M).hom ≫
        ((preadditiveYoneda.obj M).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
            (EvaluationNaturality.simplicialScalarChainMap (R := R) f).op) := by
  ext n : 1
  apply AddCommGrpCat.ext
  intro c
  apply ModuleCat.hom_ext
  change ChainDual.degreewiseChainDualEquiv K M n ((Singular.Functor.simplicialPullback M f).f n c) =
    (ChainDual.degreewiseChainDualEquiv L M n c).comp
      ((EvaluationNaturality.simplicialScalarChainMap (R := R) f).f n).hom
  exact EvaluationNaturality.degreewiseChainDualEquiv_pullback M f n c

/-- Additive Hom into an injective module preserves homology. -/
instance injectiveAdditiveYoneda_preservesHomology (M : ModuleCat.{0} R) [Injective M] :
    (preadditiveYoneda.obj M).PreservesHomology := by
  let G := forget₂ (ModuleCat.{0} (End M)) AddCommGrpCat.{0}
  change (preadditiveYonedaObj M ⋙ G).PreservesHomology
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  simpa only [ShortComplex.map_comp] using (hS.map (preadditiveYonedaObj M)).map G

/-- With injective coefficients, an actual quasi-isomorphism of scalar
simplicial chains induces an actual quasi-isomorphism of cochains. -/
theorem simplicialPullback_quasiIso_of_injective (M : ModuleCat.{0} R) [Injective M]
    {K L : SSet.{0}} (f : K ⟶ L) [QuasiIso (EvaluationNaturality.simplicialScalarChainMap (R := R) f)] :
    QuasiIso (Singular.Functor.simplicialPullback M f) := by
  let F := forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}
  let g := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (Singular.Functor.simplicialPullback M f)
  let d := ((preadditiveYoneda.obj M).mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
      (EvaluationNaturality.simplicialScalarChainMap (R := R) f).op)
  have : QuasiIso d := by dsimp only [d]; infer_instance
  have : QuasiIso (g ≫ (simplicialCochainDualIso K M).hom) := by
    change QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Singular.Functor.simplicialPullback M f) ≫ (simplicialCochainDualIso K M).hom)
    rw [simplicialCochainDualIso_naturality]
    change QuasiIso ((simplicialCochainDualIso L M).hom ≫ d)
    infer_instance
  have : QuasiIso g := quasiIso_of_comp_right
    g (simplicialCochainDualIso K M).hom
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (Singular.Functor.simplicialPullback M f) F).mp this

end

end OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
