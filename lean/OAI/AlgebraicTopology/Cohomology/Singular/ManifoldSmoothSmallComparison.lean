import OAI.AlgebraicTopology.Cohomology.Singular.IntegralCochainComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSmallQuasiIso

/-! # Manifold Smooth Small Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallComparison

noncomputable section

/-!
# Cochain comparison for actual cover-small smooth simplices

The proved smooth subdivision comparison is applied to the actual inclusion
of the small smooth simplicial set. Exact duality with injective integer
coefficients, followed by the proved scalar-restriction identification,
gives the corresponding cochain comparison over characteristic-zero fields.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothSmallQuasiIso.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Set X)

/-- Smooth cochain restriction for an actual open cover is a
quasi-isomorphism whenever the underlying integer coefficient module is
injective. -/
theorem manifoldSmoothSmallRestriction_quasiIso_of_injectiveRestriction
    {R : Type} [CommRing R] (g : ℤ →+* R) (A : ModuleCat.{0} R)
    [Injective ((ModuleCat.restrictScalars g).obj A)]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E A X U) := by
  have : QuasiIso (EvaluationNaturality.simplicialScalarChainMap (R := ℤ)
      (ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U)) :=
    AlgebraicGeometry.CycleClass.Geometric.SmoothSmallQuasiIso.Cycles.manifoldSmoothSmallIntegralChainInclusion_quasiIso E X U hopen hcover
  exact IntegralCochainComparison.simplicialPullback_quasiIso_of_injectiveIntegralRestriction g A
    (ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U)

/-- The actual all-to-small smooth cochain restriction is a
quasi-isomorphism over every characteristic-zero field. -/
theorem manifoldSmoothSmallRestriction_quasiIso
    (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E (ModuleCat.of F F) X U) := by
  have : QuasiIso (EvaluationNaturality.simplicialScalarChainMap (R := ℤ)
      (ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U)) :=
    AlgebraicGeometry.CycleClass.Geometric.SmoothSmallQuasiIso.Cycles.manifoldSmoothSmallIntegralChainInclusion_quasiIso E X U hopen hcover
  exact IntegralCochainComparison.simplicialPullback_quasiIso_of_integral F (ManifoldSmoothSmall.manifoldSmoothSmallInclusion E X U)

/-- Rational smooth cochains are computed on the actual cover-small smooth
simplices for any open cover. -/
theorem rationalManifoldSmoothSmallRestriction_quasiIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E (ModuleCat.of ℚ ℚ) X U) :=
  manifoldSmoothSmallRestriction_quasiIso E X U ℚ hopen hcover

/-- Ordinary complex-valued smooth cochains have the same actual
open-cover comparison. -/
theorem complexManifoldSmoothSmallRestriction_quasiIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E (ModuleCat.of ℂ ℂ) X U) :=
  manifoldSmoothSmallRestriction_quasiIso E X U ℂ hopen hcover

/-- The canonical comparison on cohomology is induced by the actual
restriction map. -/
def manifoldSmoothSmallCohomologyIso
    (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of F F) X).homology n ≅
      ManifoldSmoothSmall.manifoldSmoothSmallCohomology E (ModuleCat.of F F) X U n := by
  letI := manifoldSmoothSmallRestriction_quasiIso E X U F hopen hcover
  exact isoOfQuasiIsoAt (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E (ModuleCat.of F F) X U) n

@[simp]
theorem manifoldSmoothSmallCohomologyIso_hom
    (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (manifoldSmoothSmallCohomologyIso E X U F hopen hcover n).hom =
      HomologicalComplex.homologyMap
        (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E (ModuleCat.of F F) X U) n := rfl

/-- In every degree the actual smooth cohomology restriction is bijective. -/
theorem manifoldSmoothSmallCohomologyRestriction_bijective
    (F : Type) [Field F] [CharZero F]
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap
      (ManifoldSmoothSmall.manifoldSmoothSmallRestriction E (ModuleCat.of F F) X U) n) :=
  (manifoldSmoothSmallCohomologyIso E X U F hopen hcover n).toLinearEquiv.bijective

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallComparison
