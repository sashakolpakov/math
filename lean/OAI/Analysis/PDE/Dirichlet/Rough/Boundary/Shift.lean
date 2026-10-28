import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A small globally Lipschitz displacement gives an actual global
homeomorphism, not merely a formal first-order deformation. -/
theorem exists_homeomorph_of_lipschitz_displacement [CompleteSpace E] [Nontrivial E]
    (g : E → E) {K : NNReal} (hg : LipschitzWith K g) (hK : K < 1) :
    ∃ H : E ≃ₜ E, ∀ x, H x = x + g x := by
  have happ : ApproximatesLinearOn (fun x : E ↦ x + g x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) univ K := by
    intro x hx y hy
    simpa only [ContinuousLinearEquiv.coe_refl, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.id_apply, id_eq,
      show x + g x - (y + g y) - (x-y) = g x - g y by abel] using hg.norm_sub_le x y
  have hsmall : Subsingleton E ∨ K <
      ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    right
    simpa using hK
  exact ⟨happ.toHomeomorph (fun x : E ↦ x + g x) hsmall, fun _ ↦ rfl⟩

def cutoffShift (η : E → ℝ) (v : E) (t : ℝ) (x : E) : E := x + (t * η x) • v

theorem contDiff_cutoffShift {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (v : E) :
    ContDiff ℝ ∞ (fun tx : ℝ × E ↦ cutoffShift η v tx.1 tx.2) := by
  exact contDiff_snd.add ((contDiff_fst.mul (hη.comp contDiff_snd)).smul contDiff_const)

theorem cutoffShift_zero (η : E → ℝ) (v x : E) : cutoffShift η v 0 x = x := by
  simp [cutoffShift]

theorem cutoffShift_eq_self {η : E → ℝ} (v : E) (t : ℝ) {x : E} (hx : η x = 0) :
    cutoffShift η v t x = x := by simp [cutoffShift, hx]

theorem cutoffShift_preserves_linear (η : E → ℝ) (v : E) (t : ℝ)
    (ℓ : E →L[ℝ] ℝ) (hv : ℓ v = 0) (x : E) :
    ℓ (cutoffShift η v t x) = ℓ x := by simp [cutoffShift, hv]

theorem cutoffShift_displacement_lipschitz {η : E → ℝ} {K : NNReal}
    (hη : LipschitzWith K η) (v : E) (t : ℝ) :
    LipschitzWith (‖t‖₊ * K * ‖v‖₊) (fun x ↦ (t * η x) • v) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [← sub_smul, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_mul]
  change |t| * |η x - η y| * ‖v‖ ≤ (|t| * (K : ℝ) * ‖v‖) * ‖x-y‖
  calc
    _ ≤ |t| * ((K : ℝ) * ‖x-y‖) * ‖v‖ := by
      gcongr
      simpa only [Real.norm_eq_abs] using hη.norm_sub_le x y
    _ = _ := by ring

theorem cutoffShift_homeomorph [CompleteSpace E] [Nontrivial E]
    {η : E → ℝ} {K : NNReal} (hη : LipschitzWith K η) (v : E) (t : ℝ)
    (ht : ‖t‖₊ * K * ‖v‖₊ < 1) :
    ∃ H : E ≃ₜ E, ∀ x, H x = cutoffShift η v t x :=
  exists_homeomorph_of_lipschitz_displacement _
    (cutoffShift_displacement_lipschitz hη v t) ht

theorem eventually_cutoffShift_homeomorph [CompleteSpace E] [Nontrivial E]
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (v : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ H : E ≃ₜ E, ∀ x, H x = cutoffShift η v t x := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hη (by simp)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖₊ * K * ‖v‖₊ < 1 := by
    have hcont : Continuous (fun t : ℝ ↦ ‖t‖₊ * K * ‖v‖₊) := by fun_prop
    exact hcont.continuousAt.eventually_lt continuousAt_const (by simp)
  exact hsmall.mono (fun t ht ↦ cutoffShift_homeomorph hK v t ht)

end OAI.Analysis.PDE.Dirichlet
