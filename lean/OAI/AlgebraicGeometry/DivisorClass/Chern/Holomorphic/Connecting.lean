import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ShortExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! # Connecting -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting

noncomputable section

/-! The actual connecting map of the holomorphic exponential sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- Degree-one unit-sheaf cohomology, with its ordinary derived-functor meaning. -/
abbrev holomorphicUnitCohomology := CategoryTheory.Sheaf.H (Sheaves.holomorphicUnitsSheaf E M) 1

/-- Ordinary degree-two cohomology of the locally constant integral sheaf. -/
abbrev integralSheafCohomologyTwo := CategoryTheory.Sheaf.H (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)) 2

/-- The exponential connecting map, induced by the proved short exact sequence. -/
def holomorphicExponentialConnecting :
    holomorphicUnitCohomology E M →+ integralSheafCohomologyTwo M :=
  (ShortExact.holomorphicExponentialSequence_shortExact E M).extClass.postcomp
    ((constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ))) (rfl : 1 + 1 = 2)

/-- The obstruction measured by the degree-two holomorphic cohomology group. -/
def holomorphicPeriodCohomologyMap :
    integralSheafCohomologyTwo M →+
      CategoryTheory.Sheaf.H (Sheaves.holomorphicFunctionSheaf E M) 2 :=
  CategoryTheory.Sheaf.H.map (PeriodSequence.holomorphicPeriodSheafMap E M) 2

theorem holomorphicExponentialConnecting_period (u : holomorphicUnitCohomology E M) :
    holomorphicPeriodCohomologyMap E M (holomorphicExponentialConnecting E M u) = 0 := by
  change (u.comp (ShortExact.holomorphicExponentialSequence_shortExact E M).extClass
    (rfl : 1 + 1 = 2)).comp (Ext.mk₀ (PeriodSequence.holomorphicPeriodSheafMap E M)) (add_zero 2) = 0
  have hz : (ShortExact.holomorphicExponentialSequence_shortExact E M).extClass.comp
      (Ext.mk₀ (PeriodSequence.holomorphicPeriodSheafMap E M)) (add_zero 1) = 0 :=
    (ShortExact.holomorphicExponentialSequence_shortExact E M).extClass_comp
  rw [Ext.comp_assoc_of_third_deg_zero, hz, Ext.comp_zero]

/-- Exactness supplies a unit-sheaf class for every integral class with zero holomorphic image. -/
theorem exists_holomorphicUnitCohomology_of_period_zero
    (a : integralSheafCohomologyTwo M) (ha : holomorphicPeriodCohomologyMap E M a = 0) :
    ∃ u : holomorphicUnitCohomology E M, holomorphicExponentialConnecting E M u = a := by
  exact Ext.covariant_sequence_exact₁ _ (ShortExact.holomorphicExponentialSequence_shortExact E M)
    a ha (rfl : 1 + 1 = 2)

theorem holomorphicExponentialConnecting_range :
    (holomorphicExponentialConnecting E M).range =
      (holomorphicPeriodCohomologyMap E M).ker := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    exact holomorphicExponentialConnecting_period E M u
  · exact exists_holomorphicUnitCohomology_of_period_zero E M a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting
