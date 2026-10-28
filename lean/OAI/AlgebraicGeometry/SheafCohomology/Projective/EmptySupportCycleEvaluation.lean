import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles

/-! # Empty Support Cycle Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.EmptySupportCycleEvaluation

noncomputable section

/-! The coefficient of an empty-support zero cycle can be read at any cover member. -/

open _root_.AlgebraicGeometry
universe u v
variable (R : Type u) [CommRing R] {ι : Type v} [LinearOrder ι]

theorem orderedEmptySupportCyclesEquiv_eq_component (N : Set ι) (hN : N = ∅)
    (i : ι) (s : (OrderedCechSupportContraction.orderedCechSupportDifferential R N 0).ker)
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv R N hN i s = s.val.val a := by
  subst N
  exact (OrderedCechZeroCycles.orderedSupportZeroCycle_constant R s i a).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.EmptySupportCycleEvaluation
