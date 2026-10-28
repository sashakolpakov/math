import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective

/-! # Integral Cochain Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.IntegralCochainComparison

noncomputable section

/-!
# Cochain comparison from actual integral simplicial chains

An integral simplicial chain quasi-isomorphism induces a cochain
quasi-isomorphism with coefficients whose underlying integer module is
injective. Characteristic-zero fields have that property by divisibility.
The proof uses the actual cochain duality and exact scalar-restriction
isomorphisms already constructed.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Integral chain comparison implies cochain comparison with any coefficient
module whose genuine restriction to the integers is injective. -/
theorem simplicialPullback_quasiIso_of_injectiveIntegralRestriction
    {R : Type} [CommRing R] (g : ℤ →+* R) (A : ModuleCat.{0} R)
    [Injective ((ModuleCat.restrictScalars g).obj A)]
    {K L : SSet.{0}} (f : K ⟶ L)
    [QuasiIso (EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f)] :
    QuasiIso (Functor.simplicialPullback A f) := by
  let G := ModuleCat.restrictScalars g
  have hIntegral : QuasiIso (Functor.simplicialPullback (G.obj A) f) :=
    InjectiveChainDual.simplicialPullback_quasiIso_of_injective (G.obj A) f
  have hRestricted : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Functor.simplicialPullback A f)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (IntegralCoefficientInjective.simplicialCochainsRestrictScalarsArrowIso g A f)).mpr hIntegral
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (Functor.simplicialPullback A f) G).mp hRestricted

/-- In particular, integral chain comparison implies ordinary cochain
comparison over every characteristic-zero field. -/
theorem simplicialPullback_quasiIso_of_integral
    (F : Type) [Field F] [CharZero F] {K L : SSet.{0}} (f : K ⟶ L)
    [QuasiIso (EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f)] :
    QuasiIso (Functor.simplicialPullback (ModuleCat.of F F) f) := by
  have := IntegralCoefficientInjective.injective_restrictScalars_field F (algebraMap ℤ F)
  exact simplicialPullback_quasiIso_of_injectiveIntegralRestriction
    (algebraMap ℤ F) (ModuleCat.of F F) f

end

end OAI.AlgebraicTopology.Cohomology.Singular.IntegralCochainComparison
