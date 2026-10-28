import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.MarkedIntersection
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ProductOrder

/-! # Companion Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CompanionOrder.Construction

noncomputable section

/-! Companion order bounds and residual-order decrease on arbitrary smooth affine algebras. -/

universe u

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

include k in
theorem smooth_companion_order_iff (J M q : Ideal R) [q.IsMaximal]
    (m b : ℕ) (hm : 0 < m) (hmb : m < b) :
    CompanionCenter.Construction.companionIdeal J M m b ≤ q ^ (m * (b - m)) ↔ J ≤ q ^ m ∧ M ≤ q ^ (b - m) :=
  MarkedIntersection.Construction.smooth_closedPoint_markedIntersection_order_iff k J M q m (b - m) hm (by omega)

include k in
theorem smooth_companion_order_bound (J M q : Ideal R) [q.IsMaximal]
    (m b : ℕ) (hmb : m < b) (hJ : ¬ J ≤ q ^ (m + 1)) :
    ¬ CompanionCenter.Construction.companionIdeal J M m b ≤ q ^ (m * (b - m) + 1) := by
  intro h
  have hp : J ^ (b - m) ≤ q ^ (m * (b - m) + 1) := le_sup_left.trans h
  exact hJ ((ProductOrder.Construction.smooth_closedPoint_power_strict_order_iff k J q m (b - m) (by omega)).mp hp)

include k in
/-- On the exact residual-order stratum, the companion condition is exactly
the unresolved product condition, without any global coordinate assumption. -/
theorem smooth_companion_residual_stratum_order_iff (J M q : Ideal R) [q.IsMaximal]
    (m b : ℕ) (hm : 0 < m) (hmb : m < b)
    (hJ : J ≤ q ^ m) (hJ1 : ¬ J ≤ q ^ (m + 1)) :
    CompanionCenter.Construction.companionIdeal J M m b ≤ q ^ (m * (b - m)) ↔ M * J ≤ q ^ b := by
  rw [smooth_companion_order_iff k J M q m b hm hmb]
  simp only [hJ, true_and]
  exact (ProductOrder.Construction.smooth_closedPoint_product_order_iff k J M q m b (Nat.le_of_lt hmb) hJ hJ1).symm

variable [CharZero k]

theorem smooth_relative_terminal_iff_closed_power (J : Ideal R) (b : ℕ) (hb : 0 < b) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) = ⊤ ↔
      ∀ (q : Ideal R) [q.IsMaximal], ¬ J ≤ q ^ b := by
  rw [ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k J (b - 1)]
  simp only [Nat.sub_add_cancel hb, ClosedWeightedOrder.Construction.closedPoint_local_order_iff]

theorem smooth_closedPoint_order_iff_differential_control (J q : Ideal R) [q.IsMaximal]
    (b : ℕ) (hb : 0 < b) : J ≤ q ^ b ↔ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) ≤ q := by
  simpa only [Nat.sub_add_cancel hb, ClosedWeightedOrder.Construction.closedPoint_local_order_iff] using
    ClosedPointChartTransport.Construction.smooth_closedPoint_order_iff_relative_differentialIdeal k J q (b - 1)

/-- The companion has a differential bound at its own control whenever
the residual ideal has its prescribed maximal-order bound. -/
theorem smooth_companion_relative_differential_bound (J M : Ideal R) (m b : ℕ)
    (hmb : m < b) (hJ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (CompanionCenter.Construction.companionIdeal J M m b) (m * (b - m)) = ⊤ := by
  apply (ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k _ _).mpr
  intro q _ hlocal
  have hJ1 : ¬ J ≤ q ^ (m + 1) := by
    intro h
    exact ((ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k J m).mp hJ q)
      ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (m + 1)).mpr h)
  exact smooth_companion_order_bound k J M q m b hmb hJ1
    ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff _ q _).mp hlocal)

/-- Clearing the companion removes the residual maximum-order stratum
from the remaining product order locus. The statement is a native ideal
equality and can be used after every actual chart refinement. -/
theorem smooth_companion_terminal_residual_drop (J M : Ideal R) (m b : ℕ)
    (hm : 0 < m) (hmb : m < b)
    (hJ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m = ⊤)
    (hC : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (CompanionCenter.Construction.companionIdeal J M m b) (m * (b - m) - 1) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (M * J) (b - 1) ⊔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) = ⊤ := by
  by_contra hproper
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hproper
  let : q.IsMaximal := hq
  have hprod : M * J ≤ q ^ b := (smooth_closedPoint_order_iff_differential_control k _ q b (by omega)).mpr
    (le_sup_left.trans hle)
  have hJm : J ≤ q ^ m := (smooth_closedPoint_order_iff_differential_control k J q m hm).mpr
    (le_sup_right.trans hle)
  have hJ1 : ¬ J ≤ q ^ (m + 1) := by
    intro h
    exact ((ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k J m).mp hJ q)
      ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (m + 1)).mpr h)
  have hcomp := (smooth_companion_residual_stratum_order_iff k J M q m b hm hmb hJm hJ1).mpr hprod
  exact ((smooth_relative_terminal_iff_closed_power k _ (m * (b - m))
    (Nat.mul_pos hm (by omega))).mp hC q) hcomp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CompanionOrder.Construction
