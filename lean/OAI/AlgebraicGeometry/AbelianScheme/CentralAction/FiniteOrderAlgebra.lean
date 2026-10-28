import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives

/-! # Finite Order Algebra -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrderAlgebra.Construction

/-! Elementary finite-order operations used for integral clearing and
for choosing one common exponent across the geometric and linear actions. -/

theorem finite_order_left_of_commuting_product {G : Type*} [Monoid G] {x y : G}
    (h : Commute x y) (hxy : IsOfFinOrder (x * y)) (hy : IsOfFinOrder y) : IsOfFinOrder x := by
  obtain ⟨n, hn, hxy⟩ := hxy.exists_pow_eq_one
  obtain ⟨m, hm, hy⟩ := hy.exists_pow_eq_one
  have hxy' : (x * y) ^ (n * m) = 1 := by rw [pow_mul, hxy, one_pow]
  have hy' : y ^ (n * m) = 1 := by rw [Nat.mul_comm, pow_mul, hy, one_pow]
  have hx := h.mul_pow (n * m)
  rw [hxy', hy', mul_one] at hx
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n * m, Nat.mul_pos hn hm, hx.symm⟩

theorem centralCoset_commute (s q : ℕ) [Fact q.Prime] (a b : Fin s → ℤ) (h k : ℤ) :
    Commute (CentralRepresentatives.Construction.centralCoset s q a h) (CentralRepresentatives.Construction.centralCoset s q b k) := by
  change _ * _ = _ * _
  rw [CentralRepresentatives.Construction.centralCoset_mul, CentralRepresentatives.Construction.centralCoset_mul]
  simp only [Int.add_comm]

open _root_.CategoryTheory in
theorem aut_finite_of_hom {C : Type*} [Category C] {X : C} (e : Aut X)
    (h : IsOfFinOrder (End.of e.hom)) : IsOfFinOrder e := by
  obtain ⟨n, hn, he⟩ := h.exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hn, ?_⟩
  apply Iso.ext
  change (Aut.toEnd X) (e ^ n) = (Aut.toEnd X) 1
  rw [map_pow, map_one]
  exact he

theorem four_finite_common_power {A B C D : Type*}
    [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    (a : A) (b : B) (c : C) (d : D)
    (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) (hc : IsOfFinOrder c) (hd : IsOfFinOrder d) :
    ∃ n : ℕ, 0 < n ∧ a ^ n = 1 ∧ b ^ n = 1 ∧ c ^ n = 1 ∧ d ^ n = 1 := by
  let n := orderOf a * orderOf b * orderOf c * orderOf d
  refine ⟨n, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha.orderOf_pos hb.orderOf_pos) hc.orderOf_pos)
    hd.orderOf_pos, ?_, ?_, ?_, ?_⟩
  all_goals apply orderOf_dvd_iff_pow_eq_one.mp
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact dvd_mul_left _ _

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrderAlgebra.Construction
