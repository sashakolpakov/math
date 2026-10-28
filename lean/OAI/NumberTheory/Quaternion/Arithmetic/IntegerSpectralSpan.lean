import OAI.NumberTheory.Quaternion.Arithmetic.SpectralRationalSpan

/-! # Integer Spectral Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegerSpectralSpan

noncomputable section

/-! Finite eigenvalue families are spanned by integer-valued additive
spectral changes. Each such change integrates to a cocharacter once it
is applied to an algebraic infinitesimal matrix. -/

open scoped Classical
open Set

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]

def integerSpectralVectors (w : ι → K) : Set (ι → K) :=
  {z | ∃ m : ι → ℤ, z = (fun i => (m i : K)) ∧
    ∃ ψ : K →+ K, ∀ i, ψ (w i) = (m i : K)}

theorem rational_projection_mem_integer_spectral_span (w : ι → K) (φ : K →ₗ[ℚ] ℚ) :
    (fun i => (φ (w i) : K)) ∈ Submodule.span K (integerSpectralVectors w) := by
  obtain ⟨D, hD, m, hm⟩ := SpectralRationalSpan.finite_rational_family_integer_multiple (fun i => φ (w i))
  let ψ : K →+ K := {
    toFun x := (D : K) * (φ x : K)
    map_zero' := by simp
    map_add' := fun x y => by simp [mul_add] }
  have hψ (i : ι) : ψ (w i) = (m i : K) := by
    have h := congrArg (Rat.castHom K) (hm i)
    change (D : K) * (φ (w i) : K) = (m i : K)
    simpa only [map_mul, Rat.coe_castHom, Rat.cast_intCast] using h.symm
  have hmem : (fun i => (m i : K)) ∈ Submodule.span K (integerSpectralVectors w) :=
    Submodule.subset_span ⟨m, rfl, ψ, hψ⟩
  have he : (fun i => (m i : K)) = (D : K) • (fun i => (φ (w i) : K)) :=
    funext fun i => (hψ i).symm
  have hD' : (D : K) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hs := (Submodule.span K (integerSpectralVectors w)).smul_mem (D : K)⁻¹ hmem
  rw [he] at hs
  simpa only [smul_smul, inv_mul_cancel₀ hD', one_smul] using hs

theorem finite_family_mem_integer_spectral_span (w : ι → K) :
    w ∈ Submodule.span K (integerSpectralVectors w) := by
  have hle : Submodule.span K
      {z : ι → K | ∃ φ : K →ₗ[ℚ] ℚ, z = fun i => (φ (w i) : K)} ≤
        Submodule.span K (integerSpectralVectors w) := by
    apply Submodule.span_le.mpr
    rintro z ⟨φ, rfl⟩
    exact rational_projection_mem_integer_spectral_span w φ
  exact hle (SpectralRationalSpan.finite_family_mem_span_rational_projections w)

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegerSpectralSpan
