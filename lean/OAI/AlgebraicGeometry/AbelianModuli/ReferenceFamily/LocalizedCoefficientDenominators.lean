import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! # Localized Coefficient Denominators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizedCoefficientDenominators

/-! Polynomial combinations of one inverted element and integral
coefficients have denominators that are powers of that same element.
A finite family admits one common such denominator. -/

variable {E : Type*} [Field E]

theorem exists_power_mul_mem_of_localized_closure
    (S : Subring E) (b z : E) (hb : b ∈ S) (hb0 : b ≠ 0) (hz : z ∈ S)
    {x : E} (hx : x ∈ Subring.closure {b⁻¹, z}) :
    ∃ n : ℕ, b ^ n * x ∈ S := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨1, by simp [hb0]⟩
      · obtain rfl := Set.mem_singleton_iff.mp hx
        exact ⟨0, by simpa using hz⟩
  | zero => exact ⟨0, by simp⟩
  | one => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨n + m, ?_⟩
      have he : b ^ (n + m) * (x + y) =
          b ^ m * (b ^ n * x) + b ^ n * (b ^ m * y) := by
        rw [pow_add]
        ring
      rw [he]
      exact S.add_mem (S.mul_mem (S.pow_mem hb m) hn)
        (S.mul_mem (S.pow_mem hb n) hm)
  | neg x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, by simpa only [mul_neg] using S.neg_mem hn⟩
  | mul x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨n + m, ?_⟩
      have he : b ^ (n + m) * (x * y) = (b ^ n * x) * (b ^ m * y) := by
        rw [pow_add]
        ring
      rw [he]
      exact S.mul_mem hn hm

theorem exists_common_power_mul_mem_of_localized_closure
    (S : Subring E) (b z : E) (hb : b ∈ S) (hb0 : b ≠ 0) (hz : z ∈ S)
    {I : Type*} [Fintype I] (x : I → E)
    (hx : ∀ i, x i ∈ Subring.closure {b⁻¹, z}) :
    ∃ n : ℕ, ∀ i, b ^ n * x i ∈ S := by
  classical
  choose n hn using fun i => exists_power_mul_mem_of_localized_closure S b z hb hb0 hz (hx i)
  refine ⟨∑ i, n i, ?_⟩
  intro i
  have hle : n i ≤ ∑ j, n j := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have he : b ^ (∑ j, n j) * x i =
      b ^ ((∑ j, n j) - n i) * (b ^ n i * x i) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [he]
  exact S.mul_mem (S.pow_mem hb _) (hn i)

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LocalizedCoefficientDenominators
