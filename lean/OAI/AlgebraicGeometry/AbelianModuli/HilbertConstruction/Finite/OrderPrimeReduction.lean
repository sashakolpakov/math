import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic

/-! # Order Prime Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.OrderPrimeReduction

noncomputable section

/-! A nonidentity finite-order group element gives a nonidentity element of prime order in the same group. -/

universe u

variable {G : Type u} [Group G]

theorem finiteOrder_exists_prime_order (u : G) (hu : IsOfFinOrder u) (hne : u ≠ 1) :
    ∃ (p : ℕ) (v : G), p.Prime ∧ v ^ p = 1 ∧ v ≠ 1 := by
  have hn1 : orderOf u ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
  let v := u ^ (orderOf u / p)
  have hv : orderOf v = p := orderOf_pow_orderOf_div hu.orderOf_pos.ne' hpd
  have hvp : v ^ p = 1 := hv ▸ pow_orderOf_eq_one v
  have hv1 : v ≠ 1 := by
    intro he
    have hpo : p = 1 := hv.symm.trans (he ▸ orderOf_one)
    exact hp.ne_one hpo
  exact ⟨p, v, hp, hvp, hv1⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.OrderPrimeReduction
