import OAI.Analysis.PDE.Weak.SobolevWeakComplexTest
import OAI.Analysis.Normed.Function.Sobolev.FourierRegularity

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory FourierTransform Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

def fourierKernel {d : ℕ} (ξ x : Space d) : ℂ :=
  Real.fourierChar (-(inner ℝ x ξ))

@[simp] theorem norm_fourierKernel {d : ℕ} (ξ x : Space d) :
    ‖fourierKernel ξ x‖ = 1 := by
  simp [fourierKernel]

theorem contDiff_fourierKernel {d : ℕ} (ξ : Space d) :
    ContDiff ℝ 1 (fourierKernel ξ) := by
  unfold fourierKernel
  simp only [Real.fourierChar_apply]
  change ContDiff ℝ 1 (fun x : Space d ↦
    Complex.exp (Complex.ofRealCLM (2 * Real.pi * -(inner ℝ x ξ)) * Complex.I))
  have hi : ContDiff ℝ 1 (fun x : Space d ↦ inner ℝ x ξ) :=
    ((innerSL ℝ).flip ξ).contDiff
  have hr : ContDiff ℝ 1 (fun x : Space d ↦ 2 * Real.pi * -(inner ℝ x ξ)) :=
    contDiff_const.mul hi.neg
  have hz := Complex.ofRealCLM.contDiff.comp hr
  exact (hz.mul contDiff_const).cexp

theorem fderiv_fourierKernel {d : ℕ} (ξ x v : Space d) :
    fderiv ℝ (fourierKernel ξ) x v =
      (-2 * Real.pi * Complex.I * (inner ℝ v ξ : ℂ)) * fourierKernel ξ x := by
  simpa only [fourierKernel] using!
    Real.fderiv_fourierChar_neg_bilinear_left_apply (innerSL ℝ) x v ξ

theorem fourier_eq_kernel {d : ℕ} (f : Space d → ℂ) (ξ : Space d) :
    𝓕 f ξ = ∫ x, f x * fourierKernel ξ x := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, fourierKernel, mul_comm]

theorem integrable_mul_fourierKernel {d : ℕ} {f : Space d → ℂ}
    (hf : Integrable f) (ξ : Space d) :
    Integrable (fun x ↦ f x * fourierKernel ξ x) := by
  apply hf.norm.mono'
    (hf.aestronglyMeasurable.mul (contDiff_fourierKernel ξ).continuous.aestronglyMeasurable)
  exact Eventually.of_forall fun x ↦ by simp

def realFourier {d : ℕ} (f : Space d → ℝ) : Space d → ℂ :=
  𝓕 (fun x ↦ (f x : ℂ))

/-- The exact Fourier multiplier identity for an actual weak derivative.
The input functions need not have classical derivatives or be continuous. -/
theorem realFourier_weakDerivative {d : ℕ} {v : Space d} {u g : Space d → ℝ}
    (h : OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative volume v u g)
    {K : Set (Space d)} (hK : IsCompact K)
    (huK : ∀ᵐ x, x ∉ K → u x = 0) (hgK : ∀ᵐ x, x ∉ K → g x = 0)
    (hu : Integrable u) (hg : Integrable g) (ξ : Space d) :
    realFourier g ξ =
      (2 * Real.pi * Complex.I * (inner ℝ v ξ : ℂ)) * realFourier u ξ := by
  let c : ℂ := 2 * Real.pi * Complex.I * (inner ℝ v ξ : ℂ)
  have hd (x : Space d) : fderiv ℝ (fourierKernel ξ) x v = -c * fourierKernel ξ x := by
    rw [fderiv_fourierKernel]
    dsimp only [c]
    ring
  have hiu := integrable_mul_fourierKernel hu.ofReal ξ
  have hig := integrable_mul_fourierKernel hg.ofReal ξ
  have hid : Integrable (fun x ↦ (u x : ℂ) * fderiv ℝ (fourierKernel ξ) x v) := by
    simpa only [hd, mul_left_comm, mul_assoc] using! hiu.const_mul (-c)
  have he := h.complex_test_of_compact_support hK huK hgK (contDiff_fourierKernel ξ) hig hid
  change 𝓕 (fun x ↦ (g x : ℂ)) ξ = c * 𝓕 (fun x ↦ (u x : ℂ)) ξ
  rw [fourier_eq_kernel, fourier_eq_kernel]
  rw [he]
  simp_rw [hd]
  have hfun : (fun x ↦ (u x : ℂ) * (-c * fourierKernel ξ x)) =
      (fun x ↦ -c * ((u x : ℂ) * fourierKernel ξ x)) := by
    funext x
    ring
  rw [hfun, integral_const_mul]
  ring

end OAI.Analysis.Normed.Function.Sobolev
