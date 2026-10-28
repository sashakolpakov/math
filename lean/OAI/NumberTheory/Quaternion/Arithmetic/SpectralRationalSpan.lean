import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Localization.NumDen

/-! # Spectral Rational Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SpectralRationalSpan

noncomputable section

/-! A finite family of characteristic-zero eigenvalues is spanned by
its rational additive projections. Denominators of each projected finite
family can be cleared simultaneously. -/

open scoped Classical
open Set _root_.Module

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]

theorem finite_family_mem_span_rational_projections (w : ι → K) :
    w ∈ Submodule.span K
      {z : ι → K | ∃ φ : K →ₗ[ℚ] ℚ, z = fun i => (φ (w i) : K)} := by
  let V := Submodule.span ℚ (range w)
  let : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (finite_range w)
  let b := Module.finBasis ℚ V
  have hext (j : Fin (Module.finrank ℚ V)) :
      ∃ φ : K →ₗ[ℚ] ℚ, φ.comp V.subtype = b.coord j := (b.coord j).exists_extend
  choose φ hφ using hext
  let z := fun j i => (φ j (w i) : K)
  have hz (j : Fin (Module.finrank ℚ V)) : z j ∈ Submodule.span K
      {z : ι → K | ∃ φ : K →ₗ[ℚ] ℚ, z = fun i => (φ (w i) : K)} :=
    Submodule.subset_span ⟨φ j, rfl⟩
  have he : (∑ j, (b j : K) • z j) = w := by
    funext i
    rw [Finset.sum_apply]
    change (∑ j, (b j : K) * (φ j (w i) : K)) = w i
    let wi : V := ⟨w i, Submodule.subset_span (mem_range_self i)⟩
    have hcoord (j : Fin (Module.finrank ℚ V)) : φ j (w i) = b.repr wi j :=
      LinearMap.congr_fun (hφ j) wi
    have hb : ∑ j, (b.repr wi j : ℚ) • (b j : K) = w i := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using congrArg Subtype.val (b.sum_repr wi)
    simpa only [hcoord, Rat.smul_def, mul_comm] using hb
  have hsum : (∑ j, (b j : K) • z j) ∈ Submodule.span K
      {z : ι → K | ∃ φ : K →ₗ[ℚ] ℚ, z = fun i => (φ (w i) : K)} :=
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ (b j : K) (hz j))
  exact he ▸ hsum

theorem finite_rational_family_integer_multiple (a : ι → ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ z : ι → ℤ, ∀ i, (z i : ℚ) = (D : ℚ) * a i := by
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) a
  choose z hz using hD
  refine ⟨D.val, mem_nonZeroDivisors_iff_ne_zero.mp D.property, z, ?_⟩
  intro i
  simpa only [algebraMap_int_eq, Int.coe_castRingHom, zsmul_eq_mul] using hz i

end

end OAI.NumberTheory.Quaternion.Arithmetic.SpectralRationalSpan
