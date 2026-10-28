import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodRiemannForm
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Period Hermitian -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# The positive Hermitian form on the CM period space

The imaginary part is exactly the previously constructed integral Riemann
form. The convention is conjugate linear in the first argument and complex
linear in the second, so fixing a lattice vector in the first argument
gives a holomorphic function of the period variable.
-/

open scoped Classical _root_.NumberField ContDiff

open _root_.NumberField

variable (E : Type*) [Field E] [NumberField E]

/-- The weighted Hermitian form, presented as a complex linear map in its second argument. -/
def PeriodHermitian.cmPeriodHermitian (w : InfinitePlace E → ℝ) (x : PeriodSpace.CMPeriodSpace E) : PeriodSpace.CMPeriodSpace E →ₗ[ℂ] ℂ :=
  ∑ v, ((w v : ℂ) * star (x v)) • LinearMap.proj v

theorem PeriodHermitian.cmPeriodHermitian_apply (w : InfinitePlace E → ℝ) (x y : PeriodSpace.CMPeriodSpace E) :
    PeriodHermitian.cmPeriodHermitian E w x y = ∑ v, (w v : ℂ) * star (x v) * y v := by
  simp [PeriodHermitian.cmPeriodHermitian]

theorem PeriodHermitian.cmPeriodHermitian_add_left (w : InfinitePlace E → ℝ) (x y z : PeriodSpace.CMPeriodSpace E) :
    PeriodHermitian.cmPeriodHermitian E w (x + y) z = PeriodHermitian.cmPeriodHermitian E w x z + PeriodHermitian.cmPeriodHermitian E w y z := by
  simp only [PeriodHermitian.cmPeriodHermitian_apply, Pi.add_apply, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem PeriodHermitian.cmPeriodHermitian_smul_left (w : InfinitePlace E → ℝ) (a : ℂ) (x y : PeriodSpace.CMPeriodSpace E) :
    PeriodHermitian.cmPeriodHermitian E w (a • x) y = star a * PeriodHermitian.cmPeriodHermitian E w x y := by
  simp only [PeriodHermitian.cmPeriodHermitian_apply, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem PeriodHermitian.cmPeriodHermitian_symm (w : InfinitePlace E → ℝ) (x y : PeriodSpace.CMPeriodSpace E) :
    PeriodHermitian.cmPeriodHermitian E w y x = star (PeriodHermitian.cmPeriodHermitian E w x y) := by
  simp only [PeriodHermitian.cmPeriodHermitian_apply, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem PeriodHermitian.cmPeriodHermitian_im (w : InfinitePlace E → ℝ) (x y : PeriodSpace.CMPeriodSpace E) :
    (PeriodHermitian.cmPeriodHermitian E w x y).im = PeriodRiemannForm.cmPeriodForm E w x y := by
  rw [PeriodHermitian.cmPeriodHermitian_apply, Complex.im_sum, PeriodRiemannForm.cmPeriodForm_apply]
  apply Finset.sum_congr rfl
  intro v _
  change ((w v : ℂ) * (starRingEnd ℂ) (x v) * y v).im = _
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem PeriodHermitian.cmPeriodHermitian_self (w : InfinitePlace E → ℝ) (x : PeriodSpace.CMPeriodSpace E) :
    PeriodHermitian.cmPeriodHermitian E w x x = (PeriodRiemannForm.cmPeriodForm E w x (Complex.I • x) : ℂ) := by
  rw [PeriodHermitian.cmPeriodHermitian_apply, PeriodRiemannForm.cmPeriodForm_complex_self]
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  change (w v : ℂ) * (starRingEnd ℂ) (x v) * x v = _
  rw [mul_assoc, mul_comm ((starRingEnd ℂ) (x v)), Complex.mul_conj]

variable [Algebra ℚ E] [IsCMField E]

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- The positive Hermitian form belonging to the integral CM Riemann form. -/
def TypeHodgeStructure.CMEmbeddingType.periodHermitian (x : PeriodSpace.CMPeriodSpace E) : PeriodSpace.CMPeriodSpace E →ₗ[ℂ] ℂ :=
  PeriodHermitian.cmPeriodHermitian E (fun v =>
    2 * (ε.placeEmbedding v (ε.polarizationMultiplier • ε.imaginaryElement)).im) x

@[simp]
theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_zero_left (x : PeriodSpace.CMPeriodSpace E) : ε.periodHermitian 0 x = 0 := by
  simp [TypeHodgeStructure.CMEmbeddingType.periodHermitian, PeriodHermitian.cmPeriodHermitian_apply]

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_add_left (x y z : PeriodSpace.CMPeriodSpace E) :
    ε.periodHermitian (x + y) z = ε.periodHermitian x z + ε.periodHermitian y z :=
  PeriodHermitian.cmPeriodHermitian_add_left E _ x y z

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_symm (x y : PeriodSpace.CMPeriodSpace E) :
    ε.periodHermitian y x = star (ε.periodHermitian x y) := PeriodHermitian.cmPeriodHermitian_symm E _ x y

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_im (x y : PeriodSpace.CMPeriodSpace E) :
    (ε.periodHermitian x y).im = ε.periodRiemannForm x y := PeriodHermitian.cmPeriodHermitian_im E _ x y

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_self (x : PeriodSpace.CMPeriodSpace E) :
    ε.periodHermitian x x = (ε.periodRiemannForm x (Complex.I • x) : ℂ) :=
  PeriodHermitian.cmPeriodHermitian_self E _ x

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_positive (x : PeriodSpace.CMPeriodSpace E) (hx : x ≠ 0) :
    0 < (ε.periodHermitian x x).re := by
  rw [ε.periodHermitian_self, Complex.ofReal_re]
  exact ε.periodRiemannForm_positive x hx

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_skew (x y : PeriodSpace.CMPeriodSpace E) :
    ε.periodHermitian x y - ε.periodHermitian y x =
      2 * Complex.I * (ε.periodRiemannForm x y : ℂ) := by
  rw [ε.periodHermitian_symm x y, ← ε.periodHermitian_im]
  change ε.periodHermitian x y - (starRingEnd ℂ) (ε.periodHermitian x y) = _
  apply Complex.ext
  · simp
  · simp [mul_comm, two_mul]

theorem TypeHodgeStructure.CMEmbeddingType.periodHermitian_contDiff (x : PeriodSpace.CMPeriodSpace E) :
    ContDiff ℂ ∞ (ε.periodHermitian x) :=
  (ε.periodHermitian x).toContinuousLinearMap.contDiff

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
