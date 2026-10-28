import Mathlib
import OAI.Analysis.Calculus.Quaternion.Algebra

/-! Algebra of the wave current in `sections/current.tex`.

The complex field here represents the commutative quaternionic plane
`span(1, k)`. The order of quaternionic amplitudes is retained separately
in the outer-product lemmas.
-/

namespace OAI.Analysis.Calculus.Current

open scoped Matrix

noncomputable section

abbrev Index (d : ℕ) := Option (Option (Fin d))

/-- The row `ℓ(w) = (-w·w/2, w, 1)`, indexed by time, space, and null time. -/
def phaseRow {d : ℕ} (w : Fin d → ℂ) : Index d → ℂ
  | none => -(∑ i, w i * w i) / 2
  | some none => 1
  | some (some i) => w i

/-- The tangent vector `Vᵛ = (1, (v+W)/2, -W·v/2)`. -/
def tangentVector {d : ℕ} (v W : Fin d → ℂ) : Index d → ℂ
  | none => 1
  | some none => -(∑ i, W i * v i) / 2
  | some (some i) => (v i + W i) / 2

/-- Equation (phase-polarization), including its full off-diagonal form. -/
theorem phase_polarization {d : ℕ} (w W v : Fin d → ℂ) :
    ∑ a, phaseRow w a * tangentVector v W a =
      -(∑ i, (w i - W i) * (w i - v i)) / 2 := by
  simp only [Fintype.sum_option, phaseRow, tangentVector, mul_one, one_mul]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, div_eq_mul_inv,
    mul_add, add_mul, Finset.sum_add_distrib]
  simp_rw [show ∀ i, W i * w i = w i * W i from fun i => mul_comm _ _]
  simp only [← mul_assoc, ← Finset.sum_mul]
  ring

/-- Every current vector is killed by its own real phase row. -/
theorem phase_tangent {d : ℕ} (v W : Fin d → ℂ) :
    ∑ a, phaseRow v a * tangentVector v W a = 0 := by
  rw [phase_polarization]
  simp

/-- Every current vector is tangent to the common holomorphic background. -/
theorem background_tangent {d : ℕ} (v W : Fin d → ℂ) :
    ∑ a, phaseRow W a * tangentVector v W a = 0 := by
  rw [phase_polarization]
  simp

/-- Tangency survives a finite superposition, including complex amplitudes. -/
theorem superposition_tangent {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (amplitude : ι → ℂ) :
    ∑ a, phaseRow W a * (∑ j, tangentVector (v j) W a * amplitude j) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, background_tangent, zero_mul]
  simp

/-- The copy of the complex numbers spanned by `1` and the quaternionic `k`. -/
def complexK : ℂ →+* Quaternion ℝ where
  toFun z := ⟨z.re, 0, 0, z.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp

/-- The quaternionic unit perpendicular to the complex `k` plane. -/
def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩

theorem complexK_star (z : ℂ) : star (complexK z) = complexK (star z) := by
  ext <;> simp [complexK]

theorem qi_complexK (z : ℂ) : qi * complexK z = complexK (star z) * qi := by
  ext <;> simp [complexK, qi]

/-- The moving imaginary unit of the amplitude embedding has square `-1`. -/
theorem movingUnit_square (e : ℂ) (he : Complex.normSq e = 1) :
    (complexK e * qi) ^ 2 = -1 := by
  simp only [Complex.normSq_apply] at he
  ext <;> simp [complexK, qi, pow_two] <;> nlinarith

/-- Multiplication in the moving complex plane agrees with complex multiplication. -/
theorem movingEmbedding_mul (e : ℂ) (he : Complex.normSq e = 1) (z w : ℂ) :
    ((z.re : Quaternion ℝ) + (complexK e * qi) * (z.im : Quaternion ℝ)) *
      ((w.re : Quaternion ℝ) + (complexK e * qi) * (w.im : Quaternion ℝ)) =
    (((z * w).re : Quaternion ℝ) +
      (complexK e * qi) * ((z * w).im : Quaternion ℝ)) := by
  simp only [Complex.normSq_apply] at he
  have hp := congrArg (fun t : ℝ => t * z.im * w.im) he
  ext <;> simp [complexK, qi] <;> nlinarith [hp]

/-- The paired-current expansion, including the cross terms between distinct modes.
Here `a,b` are entries of `V`, while `c,d` are entries of `V'`. -/
theorem paired_current_expansion (a b c d e : ℂ) (f g : ℝ) :
    complexK a * ((f : Quaternion ℝ) + (g : Quaternion ℝ) * complexK e * qi) *
      star (complexK d) +
    complexK c * ((f : Quaternion ℝ) - (g : Quaternion ℝ) * complexK e * qi) *
      star (complexK b) =
    complexK ((a * star d + c * star b) * (f : ℂ)) +
      complexK ((a * d - c * b) * (g : ℂ) * e) * qi := by
  ext <;> simp [complexK, qi] <;> ring

/-- Exact quaternionic current column, preserving amplitude order. -/
def currentColumn {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ)
    (amplitude : ι → Quaternion ℝ) : Index d → Quaternion ℝ :=
  fun a => ∑ j, complexK (tangentVector (v j) W a) * star (amplitude j)

/-- Quaternionic amplitudes do not disturb the common left tangency equation. -/
theorem currentColumn_tangent {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (amplitude : ι → Quaternion ℝ) :
    ∑ a, complexK (phaseRow W a) * currentColumn W v amplitude a = 0 := by
  simp only [currentColumn, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum,
    background_tangent, map_zero, zero_mul, Finset.sum_const_zero]

/-- `A⁰ = χ χ*` from the manuscript. -/
def currentMatrix {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (amplitude : ι → Quaternion ℝ) :=
  OAI.Analysis.Calculus.Quaternion.outer (currentColumn W v amplitude)

theorem currentMatrix_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (amplitude : ι → Quaternion ℝ) :
    (currentMatrix W v amplitude).IsHermitian :=
  OAI.Analysis.Calculus.Quaternion.outer_isHermitian _

theorem currentMatrix_quadratic_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (amplitude : ι → Quaternion ℝ)
    (x : Index d → Quaternion ℝ) :
    0 ≤ (∑ a, star (x a) * (currentMatrix W v amplitude *ᵥ x) a).re :=
  OAI.Analysis.Calculus.Quaternion.outer_quadratic_nonneg _ _

/-- The image of the full interacting current is tangent to `Φ`. -/
theorem currentMatrix_image_tangent {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (amplitude : ι → Quaternion ℝ)
    (x : Index d → Quaternion ℝ) :
    ∑ a, complexK (phaseRow W a) * (currentMatrix W v amplitude *ᵥ x) a = 0 :=
  OAI.Analysis.Calculus.Quaternion.outer_image_tangent _ _ _ (currentColumn_tangent W v amplitude)

end
end OAI.Analysis.Calculus.Current
