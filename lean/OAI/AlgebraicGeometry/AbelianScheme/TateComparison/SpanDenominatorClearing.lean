import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! # Span Denominator Clearing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SpanDenominatorClearing

noncomputable section

/-! Clearing denominators on a spanning family clears denominators on
the whole algebra, with one common central power for each finite sum. -/

theorem centralPower_clear_span {R A I : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (W : Subalgebra R A) (z : W) (v : I → A)
    (hspan : Submodule.span R (Set.range v) = ⊤)
    (hv : ∀ i, ∃ n : ℕ, (z : A) ^ n * v i ∈ W) :
    ∀ x : A, ∃ n : ℕ, (z : A) ^ n * x ∈ W := by
  let P : Submodule R A := {
    carrier := {x | ∃ n : ℕ, (z : A) ^ n * x ∈ W}
    zero_mem' := ⟨0, by simp only [pow_zero, mul_zero]; exact W.zero_mem⟩
    add_mem' := by
      intro x y hx hy
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      refine ⟨n + m, ?_⟩
      have he : (z : A) ^ (n + m) * (x + y) =
          (z : A) ^ m * ((z : A) ^ n * x) + (z : A) ^ n * ((z : A) ^ m * y) := by
        rw [mul_add, pow_add]
        congr 1 <;> ac_rfl
      rw [he]
      exact W.add_mem (W.mul_mem (W.pow_mem z.property m) hn) (W.mul_mem (W.pow_mem z.property n) hm)
    smul_mem' := by
      intro r x hx
      obtain ⟨n, hn⟩ := hx
      refine ⟨n, ?_⟩
      rw [mul_smul_comm]
      exact W.smul_mem hn r }
  have hle : Submodule.span R (Set.range v) ≤ P := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hv i)
  rw [hspan] at hle
  intro x
  exact hle (Submodule.mem_top)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SpanDenominatorClearing
