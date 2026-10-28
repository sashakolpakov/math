import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.TransformRegularElements

/-! # Overlap Transitions -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.OverlapTransitions.Construction

noncomputable section

/-! Exact unit transition functions for exceptional and boundary equations. -/

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

theorem blowupChartOverlapLeft_ratio_isUnit :
    IsUnit (ChartOverlap.Construction.blowupChartOverlapLeft I a b (ExceptionalIdeal.Construction.blowupChartRatio I a b)) := by
  let := (ChartOverlap.Construction.blowupChartOverlapLeft I a b).toAlgebra
  let := ChartOverlap.Construction.blowupChartOverlapLeft_isLocalization I a b
  exact IsLocalization.Away.algebraMap_isUnit (ExceptionalIdeal.Construction.blowupChartRatio I a b)

theorem blowupChartOverlapRight_ratio_isUnit :
    IsUnit (ChartOverlap.Construction.blowupChartOverlapRight I a b (ExceptionalIdeal.Construction.blowupChartRatio I b a)) := by
  let := (ChartOverlap.Construction.blowupChartOverlapRight I a b).toAlgebra
  let := ChartOverlap.Construction.blowupChartOverlapRight_isLocalization I a b
  exact IsLocalization.Away.algebraMap_isUnit (ExceptionalIdeal.Construction.blowupChartRatio I b a)

theorem blowupChartOverlapLeft_parameter_regular :
    IsRegular (ChartOverlap.Construction.blowupChartOverlapConstants I a b a.val) := by
  let := (ChartOverlap.Construction.blowupChartOverlapLeft I a b).toAlgebra
  let := ChartOverlap.Construction.blowupChartOverlapLeft_isLocalization I a b
  let : Module.Flat (Charts.Construction.blowupChart I a) (ChartOverlap.Construction.blowupChartOverlap I a b) :=
    IsLocalization.flat _ (Submonoid.powers (ExceptionalIdeal.Construction.blowupChartRatio I a b))
  have h := ChartFlatBaseChange.Construction.flat_algebraMap_regular (S := ChartOverlap.Construction.blowupChartOverlap I a b)
    (Charts.Construction.blowupChartConstants I a a.val) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  change IsRegular (ChartOverlap.Construction.blowupChartOverlapLeft I a b (Charts.Construction.blowupChartConstants I a a.val)) at h
  rwa [ChartOverlap.Construction.blowupChartOverlapLeft_constants] at h

theorem blowupChartOverlapLeft_factorization (z : I) :
    ChartOverlap.Construction.blowupChartOverlapConstants I a b a.val *
        ChartOverlap.Construction.blowupChartOverlapLeft I a b (ExceptionalIdeal.Construction.blowupChartRatio I a z) =
      ChartOverlap.Construction.blowupChartOverlapConstants I a b z.val := by
  rw [← ChartOverlap.Construction.blowupChartOverlapLeft_constants, ← map_mul, ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio,
    ChartOverlap.Construction.blowupChartOverlapLeft_constants]

theorem blowupChartOverlapRight_factorization (z : I) :
    ChartOverlap.Construction.blowupChartOverlapConstants I a b b.val *
        ChartOverlap.Construction.blowupChartOverlapRight I a b (ExceptionalIdeal.Construction.blowupChartRatio I b z) =
      ChartOverlap.Construction.blowupChartOverlapConstants I a b z.val := by
  rw [← ChartOverlap.Construction.blowupChartOverlapRight_constants, ← map_mul, ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio,
    ChartOverlap.Construction.blowupChartOverlapRight_constants]

/-- Every divided old boundary equation changes by the same explicit unit. -/
theorem blowupChartOverlap_ratio_transition (z : I) :
    ChartOverlap.Construction.blowupChartOverlapLeft I a b (ExceptionalIdeal.Construction.blowupChartRatio I a z) =
      ChartOverlap.Construction.blowupChartOverlapLeft I a b (ExceptionalIdeal.Construction.blowupChartRatio I a b) *
        ChartOverlap.Construction.blowupChartOverlapRight I a b (ExceptionalIdeal.Construction.blowupChartRatio I b z) := by
  apply (blowupChartOverlapLeft_parameter_regular I a b).left
  calc
    _ = ChartOverlap.Construction.blowupChartOverlapConstants I a b z.val :=
      blowupChartOverlapLeft_factorization I a b z
    _ = ChartOverlap.Construction.blowupChartOverlapConstants I a b b.val *
        ChartOverlap.Construction.blowupChartOverlapRight I a b (ExceptionalIdeal.Construction.blowupChartRatio I b z) :=
      (blowupChartOverlapRight_factorization I a b z).symm
    _ = (ChartOverlap.Construction.blowupChartOverlapConstants I a b a.val *
        ChartOverlap.Construction.blowupChartOverlapLeft I a b (ExceptionalIdeal.Construction.blowupChartRatio I a b)) *
        ChartOverlap.Construction.blowupChartOverlapRight I a b (ExceptionalIdeal.Construction.blowupChartRatio I b z) := by
      rw [blowupChartOverlapLeft_factorization]
    _ = _ := mul_assoc (ChartOverlap.Construction.blowupChartOverlapConstants I a b a.val)
      (ChartOverlap.Construction.blowupChartOverlapLeft I a b (ExceptionalIdeal.Construction.blowupChartRatio I a b))
      (ChartOverlap.Construction.blowupChartOverlapRight I a b (ExceptionalIdeal.Construction.blowupChartRatio I b z))

theorem blowupChartOverlap_ratio_ideal (z : I) :
    (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}).map (ChartOverlap.Construction.blowupChartOverlapLeft I a b) =
      (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I b z}).map (ChartOverlap.Construction.blowupChartOverlapRight I a b) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
    blowupChartOverlap_ratio_transition]
  exact Ideal.span_singleton_mul_left_unit (blowupChartOverlapLeft_ratio_isUnit I a b) _

/-- The two exceptional equations generate the same ideal on the overlap. -/
theorem blowupChartOverlap_exceptional_ideal :
    Ideal.span {ChartOverlap.Construction.blowupChartOverlapConstants I a b a.val} =
      Ideal.span {ChartOverlap.Construction.blowupChartOverlapConstants I a b b.val} := by
  rw [← blowupChartOverlapLeft_factorization I a b b]
  exact (Ideal.span_singleton_mul_right_unit (blowupChartOverlapLeft_ratio_isUnit I a b) _).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.OverlapTransitions.Construction
