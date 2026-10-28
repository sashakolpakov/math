import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Glue

/-! Higher classical jet gluing for the boundary compactness step.
The piecewise function itself, not an assumed extension, is shown C³/C⁴. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_three_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (h₀ : ∀ x, ℓ x = 0 → f x = g x)
    (h₁ : ∀ x, ℓ x = 0 → fderiv ℝ f x = fderiv ℝ g x)
    (h₂ : ∀ x, ℓ x = 0 → fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x)
    (h₃ : ∀ x, ℓ x = 0 → fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x) :
    ContDiff ℝ 3 (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g) := by
  change ContDiff ℝ ((2 : WithTop ℕ∞)+1) (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g)
  apply contDiff_succ_iff_fderiv.mpr
  refine ⟨(OAI.Analysis.PDE.Schauder.contDiff_one_levelGlue ℓ hℓ f g (hf.of_le (by norm_num))
    (hg.of_le (by norm_num)) h₀ h₁).differentiable one_ne_zero, ?_, ?_⟩
  · intro h
    norm_num at h
  · have he : fderiv ℝ (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g) = OAI.Analysis.PDE.Schauder.levelGlue ℓ (fderiv ℝ f) (fderiv ℝ g) :=
      funext (OAI.Analysis.PDE.Schauder.fderiv_levelGlue ℓ hℓ f g (hf.differentiable (by norm_num))
        (hg.differentiable (by norm_num)) h₀ h₁)
    rw [he]
    exact OAI.Analysis.PDE.Schauder.contDiff_two_levelGlue ℓ hℓ _ _ (hf.fderiv_right (by norm_num))
      (hg.fderiv_right (by norm_num)) h₁ h₂ h₃

theorem contDiff_four_levelGlue (ℓ : E → ℝ) (hℓ : Continuous ℓ) (f g : E → F)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    (h₀ : ∀ x, ℓ x = 0 → f x = g x)
    (h₁ : ∀ x, ℓ x = 0 → fderiv ℝ f x = fderiv ℝ g x)
    (h₂ : ∀ x, ℓ x = 0 → fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x)
    (h₃ : ∀ x, ℓ x = 0 → fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x)
    (h₄ : ∀ x, ℓ x = 0 → fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) x) :
    ContDiff ℝ 4 (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g) := by
  change ContDiff ℝ ((3 : WithTop ℕ∞)+1) (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g)
  apply contDiff_succ_iff_fderiv.mpr
  refine ⟨(OAI.Analysis.PDE.Schauder.contDiff_one_levelGlue ℓ hℓ f g (hf.of_le (by norm_num))
    (hg.of_le (by norm_num)) h₀ h₁).differentiable one_ne_zero, ?_, ?_⟩
  · intro h
    norm_num at h
  · have he : fderiv ℝ (OAI.Analysis.PDE.Schauder.levelGlue ℓ f g) = OAI.Analysis.PDE.Schauder.levelGlue ℓ (fderiv ℝ f) (fderiv ℝ g) :=
      funext (OAI.Analysis.PDE.Schauder.fderiv_levelGlue ℓ hℓ f g (hf.differentiable (by norm_num))
        (hg.differentiable (by norm_num)) h₀ h₁)
    rw [he]
    exact contDiff_three_levelGlue ℓ hℓ _ _ (hf.fderiv_right (by norm_num))
      (hg.fderiv_right (by norm_num)) h₁ h₂ h₃ h₄

end OAI.Analysis.PDE.Elliptic
