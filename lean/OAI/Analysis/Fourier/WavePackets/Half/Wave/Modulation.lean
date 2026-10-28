import OAI.Analysis.Fourier.WavePackets.Half.Wave.CapPhase

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff FourierTransform RealInnerProductSpace

theorem angularInverse_modulate {n : ℕ} (φ : Space n → ℂ) (v x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ) x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (x-v) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  simp only [inner_sub_left,Complex.ofReal_sub]
  ring

theorem eLpNorm_angularInverse_modulate {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) (v : Space n) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ))
      1 volume = eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume := by
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ) =
      fun x => OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (x-v) := funext (angularInverse_modulate φ v)
  rw [he]
  exact eLpNorm_comp_measurePreserving
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse hφ).aestronglyMeasurable
    (measurePreserving_sub_right volume v)

theorem eLpNorm_fourierInv_modulate {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) (v : Space n) :
    eLpNorm (𝓕⁻ (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ))
      1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  have hm : Integrable (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ) := by
    apply hφ.norm.mono'
      (((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    filter_upwards [] with ξ
    simp [Complex.norm_exp]
  rw [eLpNorm_fourierInv_eq_angularInverse hm,eLpNorm_fourierInv_eq_angularInverse hφ]
  exact eLpNorm_angularInverse_modulate hφ v

theorem capTransverse_add {d : ℕ} (x y : Space (d+1)) :
    capTransverse (x+y) = capTransverse x+capTransverse y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem capTransverse_smul {d : ℕ} (c : ℝ) (x : Space (d+1)) :
    capTransverse (c • x) = c • capTransverse x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def capLinearPhaseLinear {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) : Space (d+1) →ₗ[ℝ] ℝ where
  toFun := capLinearPhase γ c
  map_add' x y := by
    simp only [capLinearPhase,PiLp.add_apply,capTransverse_add,inner_add_right,add_div]
    ring
  map_smul' a x := by
    simp only [capLinearPhase,PiLp.smul_apply,capTransverse_smul,real_inner_smul_right,
      smul_eq_mul,RingHom.id_apply]
    ring

def capLinearPhaseCLM {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) : Space (d+1) →L[ℝ] ℝ :=
  (capLinearPhaseLinear γ c).toContinuousLinearMap

theorem eLpNorm_fourierInv_cap_modulate {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : Integrable φ) (t γ : ℝ) (c : Fin d → ℝ) :
    eLpNorm (𝓕⁻ (fun ξ => Complex.exp (-Complex.I*(t*capLinearPhase γ c ξ : ℝ))*φ ξ))
      1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  let v := (toDual ℝ (Space (d+1))).symm (t • capLinearPhaseCLM γ c)
  have hv (ξ : Space (d+1)) : inner ℝ v ξ = t*capLinearPhase γ c ξ := toDual_symm_apply
  simpa only [hv] using eLpNorm_fourierInv_modulate hφ v

end OAI.Analysis.Fourier.WavePackets
