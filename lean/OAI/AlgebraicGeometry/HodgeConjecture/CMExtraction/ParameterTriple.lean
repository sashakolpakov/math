import Mathlib

/-! # Parameter Triple -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterTriple.Central

noncomputable section

/-! Construct the normalized three-parameter multiset from the three
actual Hecke eigenvalues. Repeated roots are retained; no regularity or
distinct-eigenvalue hypothesis is used. -/

open scoped Classical

variable {F : Type*} [Field F] [IsAlgClosed F]

theorem exists_normalized_parameter_triple (Q t₁ t₂ t₃ : F)
    (hQ : Q ≠ 0) (h₃ : t₃ ≠ 0) :
    ∃ α : Fin 3 → F,
      (∀ i, α i ≠ 0) ∧
      t₁ = Q * (α 0 + α 1 + α 2) ∧
      t₂ = Q * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ∧
      t₃ = α 0 * α 1 * α 2 := by
  let P : Cubic F := ⟨1, -(t₁ / Q), t₂ / Q, -t₃⟩
  have ha : P.a ≠ 0 := one_ne_zero
  obtain ⟨x, y, z, hroots⟩ := (Cubic.splits_iff_roots_eq_three (φ := RingHom.id F) ha).mp
    (IsAlgClosed.splits _)
  have hb : t₁ / Q = x + y + z := by
    have h := Cubic.b_eq_three_roots ha hroots
    simpa only [P, RingHom.id_apply, one_mul, neg_inj] using h
  have hc : t₂ / Q = x * y + x * z + y * z := by
    simpa only [P, RingHom.id_apply, one_mul] using Cubic.c_eq_three_roots ha hroots
  have hd : t₃ = x * y * z := by
    have h := Cubic.d_eq_three_roots ha hroots
    simpa only [P, RingHom.id_apply, one_mul, neg_inj] using h
  have hp : x * y * z ≠ 0 := hd ▸ h₃
  have hx : x ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1
  have hy : y ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2
  have hz : z ≠ 0 := (mul_ne_zero_iff.mp hp).2
  refine ⟨![x, y, z], ?_, ?_, ?_, hd⟩
  · intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  · change t₁ = Q * (x + y + z)
    simpa only [mul_comm Q] using (div_eq_iff hQ).mp hb
  · change t₂ = Q * (x * y + x * z + y * z)
    simpa only [mul_comm Q] using (div_eq_iff hQ).mp hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterTriple.Central
