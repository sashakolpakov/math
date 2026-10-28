import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonHolder
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Normalization

/-! Classical whole-space solvability of constant uniformly elliptic equations with C^α data. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

theorem holder_comp_linear {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∀ x y, |f (L x) - f (L y)| ≤ (H * ‖L‖ ^ α) * ‖x - y‖ ^ α := by
  intro x y
  have hn : ‖L x - L y‖ ≤ ‖L‖ * ‖x - y‖ := by simpa only [map_sub] using L.le_opNorm (x - y)
  calc
    _ ≤ H * ‖L x - L y‖ ^ α := hh _ _
    _ ≤ H * (‖L‖ * ‖x - y‖) ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα) hH
    _ = _ := by rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]; ring

def constantEllipticPotential {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  poissonPotential (f ∘ L.toContinuousLinearMap) ∘ L.symm.toContinuousLinearMap

theorem constantEllipticPotential_solves {m : ℕ} (hm : 3 ≤ m)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (constantEllipticPotential L f) ∧
      ∀ x, nondivergenceOperator (fun _ => linearEllipticMatrix L.toContinuousLinearMap)
        (constantEllipticPotential L f) x = f x := by
  let g := f ∘ L.toContinuousLinearMap
  have hg : Continuous g := hf.comp L.continuous
  have hgc : HasCompactSupport g := hfc.comp_homeomorph L.toHomeomorph
  have hgh : ∀ x y, |g x - g y| ≤ (H * ‖L.toContinuousLinearMap‖ ^ α) * ‖x - y‖ ^ α :=
    holder_comp_linear f hH hα.le hh L.toContinuousLinearMap
  have hGH : 0 ≤ H * ‖L.toContinuousLinearMap‖ ^ α := by positivity
  have hPg := contDiff_poissonPotential_holder (show 2 ≤ m by omega) g hg hgc hGH hα hα1 hgh
  have hu : ContDiff ℝ 2 (constantEllipticPotential L f) := hPg.comp L.symm.contDiff
  refine ⟨hu, ?_⟩
  intro x
  have he : constantEllipticPotential L f ∘ L.toContinuousLinearMap = poissonPotential g := by
    funext y
    simp [constantEllipticPotential, Function.comp_def, g]
  have h := laplacian_comp_linear (constantEllipticPotential L f) hu L.toContinuousLinearMap (L.symm x)
  rw [he, laplacian_poissonPotential_holder hm g hg hgc hGH hα hα1 hgh] at h
  simpa only [g, Function.comp_apply, ContinuousLinearEquiv.coe_coe, L.apply_symm_apply,
    nondivergenceOperator] using h.symm

theorem exists_constant_elliptic_solution {m : ℕ} (hm : 3 ≤ m)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∃ u : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 2 u ∧
      ∀ x, nondivergenceOperator (fun _ => A) u x = f x := by
  obtain ⟨L, hL, _⟩ := exists_elliptic_normalization A hA
  refine ⟨constantEllipticPotential L f, ?_⟩
  simpa only [hL] using constantEllipticPotential_solves hm L f hf hfc hH hα hα1 hh

end OAI.Analysis.PDE.Schauder
