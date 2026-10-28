import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneWindingComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalMultiplicity

/-! # Normal Coordinate Residue -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NormalCoordinateResidue

noncomputable section

/-!
# ChernClass: positive winding in an arbitrary genuine normal pair

The original positive singular winding of the actual normal coordinate
is the fixed primitive sign times the existing chart Thom class. Actual
pair functoriality preserves this formula when the closed support grows.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ f x)

/-- The actual normal coordinate has the already computed primitive
positive-winding coefficient in every genuine normal pair. -/
theorem normalCoordinate_supportedWinding :
    Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) P.relativeComplement
      (HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo)
      (fun y => (HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle.nonzeroRestriction P.normalCoordinate P.relativeComplement
        P.normalCoordinate_mapsTo y).property) =
      NormalWinding.normalWindingCoefficient • HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions.normalChartClass P := by
  have h := Supported.Winding.supportedWindingClass_logarithmic (TopCat.of P.neighborhood) P.relativeComplement
    (HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo)
    (fun y => (HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle.nonzeroRestriction P.normalCoordinate P.relativeComplement
      P.normalCoordinate_mapsTo y).property)
  change _ = -HodgeConjecture.DegreeTwo.NormalResidue.Constructions.normalLogarithmicResidue P at h
  rw [HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions.normalLogarithmicResidue_eq_chartClass, ← neg_smul,
    PlaneWindingComparison.neg_windingNormalCoefficient_eq_normalWindingCoefficient] at h
  exact h

/-- The actual normal-coordinate formula on a smaller complement,
expressed for any equal continuous representative of that same coordinate. -/
theorem normalCoordinate_supportedWinding_on_subset (A : Set P.neighborhood)
    (hA : A ⊆ P.relativeComplement) (g : C(A, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hcoord : ∀ y, g y = P.normalCoordinate y.val) :
    Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) A g hg =
      NormalWinding.normalWindingCoefficient • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (𝟙 (TopCat.of P.neighborhood)) hA 2 (HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions.normalChartClass P) := by
  have h := Supported.Winding.supportedWindingClass_pullback (TopCat.of P.neighborhood) P.relativeComplement
    (𝟙 (TopCat.of P.neighborhood)) A hA
    (HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo)
    (fun y => (HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle.nonzeroRestriction P.normalCoordinate P.relativeComplement
      P.normalCoordinate_mapsTo y).property)
  rw [normalCoordinate_supportedWinding P, map_smul] at h
  refine (Supported.Winding.supportedWindingClass_congr (TopCat.of P.neighborhood) A g _ hg _ ?_).trans h.symm
  apply ContinuousMap.ext
  intro y
  exact hcoord y

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NormalCoordinateResidue
