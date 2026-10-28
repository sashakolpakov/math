import OAI.RepresentationTheory.Weil.Local.QuadraticNormSquareQuotient
import OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses

/-! # Quadratic Norm Index -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex.Construction

noncomputable section

/-! The nonzero sums of two squares have index two when -1 is nonsquare over a nonarchimedean local field. -/

theorem localField_quadraticNorm_index_two
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ t : k, t ^ 2 = -1) :
    (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k).index = 2 := by
  have hi := Subgroup.relIndex_mul_index (QuadraticNormSubgroup.Construction.squareUnitsSubgroup_le_quadraticNormSubgroup (k := k))
  rw [QuadraticNormSquareQuotient.Construction.quadraticNorm_square_relIndex, FiniteSquareClasses.Construction.localField_square_index_eq_twice_normOne hnd h] at hi
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (FiniteSquareClasses.Construction.normOne_square_index_ne_zero hnd h))
  exact hi.trans (Nat.mul_comm _ _)

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex.Construction
