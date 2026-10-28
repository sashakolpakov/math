import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles

/-! # Ordered Empty Support Values -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OrderedEmptySupportValues.Cech

noncomputable section

/-! The original empty-support zero-cycle equivalence has the constant value prescribed by its coefficient. -/

open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechZeroCycles

universe u v

theorem orderedEmptySupportCyclesEquiv_symm_value (R : Type u) [CommRing R]
    {ι : Type v} [LinearOrder ι] (N : Set ι) (hN : N = ∅) (i : ι) (r : R)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    ((SheafCohomology.Projective.OrderedCechZeroCycles.orderedEmptySupportCyclesEquiv R N hN i).symm r).val.val a = r := by
  subst N
  exact (SheafCohomology.Projective.OrderedCechZeroCycles.orderedSupportZeroCycle_constant R ((SheafCohomology.Projective.OrderedCechZeroCycles.orderedZeroCyclesEquiv R i).symm r) i a).trans
    ((SheafCohomology.Projective.OrderedCechZeroCycles.orderedZeroCyclesEquiv R i).apply_symm_apply r)

end

end OAI.AlgebraicGeometry.Comparison.Betti.OrderedEmptySupportValues.Cech
