import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialBound
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationSupport

/-! Quantitative stability of the actual Newtonian solution and its first two derivatives. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem second_fderiv_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact ((hf.differentiable (by norm_num) y).hasFDerivAt.sub
      (hg.differentiable (by norm_num) y).hasFDerivAt).fderiv
  rw [he]
  exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt.sub
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt).fderiv

theorem newtonianPotential_derivative_sub {m : ℕ} (hm : 1 ≤ m)
    (f g : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (newtonianPotential (fun y => f y - g y)) x =
      fderiv ℝ (newtonianPotential f) x - fderiv ℝ (newtonianPotential g) x := by
  rw [newtonianPotential_sub hm f g hf.continuous hg.continuous hfc hgc]
  exact (((contDiff_newtonianPotential hm f hf hfc).differentiable (by norm_num) x).hasFDerivAt.sub
    ((contDiff_newtonianPotential hm g hg hgc).differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem newtonianPotential_second_derivative_sub {m : ℕ} (hm : 1 ≤ m)
    (f g : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fderiv ℝ (newtonianPotential (fun y => f y - g y))) x =
      fderiv ℝ (fderiv ℝ (newtonianPotential f)) x - fderiv ℝ (fderiv ℝ (newtonianPotential g)) x := by
  rw [newtonianPotential_sub hm f g hf.continuous hg.continuous hfc hgc]
  exact second_fderiv_sub _ _ (contDiff_newtonianPotential hm f hf hfc) (contDiff_newtonianPotential hm g hg hgc) x

theorem newtonian_solution_stability {m : ℕ} (hm : 2 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f g : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 f → ContDiff ℝ 2 g → HasCompactSupport f → HasCompactSupport g →
      ∀ H U I, 0 ≤ H → 0 ≤ U → 0 ≤ I →
      (∀ x y, |(f x - g x) - (f y - g y)| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, |f x - g x| ≤ U) → (∫ y, |f y - g y|) ≤ I →
      (∀ x, |newtonianPotential f x - newtonianPotential g x| ≤ C * (H + U + I)) ∧
      (∀ x, ‖fderiv ℝ (newtonianPotential f) x - fderiv ℝ (newtonianPotential g) x‖ ≤ C * (H + U + I)) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x -
        fderiv ℝ (fderiv ℝ (newtonianPotential g)) x‖ ≤ C * (H + U + I)) ∧
      (∀ x y, ‖(fderiv ℝ (fderiv ℝ (newtonianPotential f)) x -
        fderiv ℝ (fderiv ℝ (newtonianPotential g)) x) -
        (fderiv ℝ (fderiv ℝ (newtonianPotential f)) y -
        fderiv ℝ (fderiv ℝ (newtonianPotential g)) y)‖ ≤ C * H * ‖x - y‖ ^ α) := by
  obtain ⟨C₁, hC₁, hc₁⟩ := newtonianPotential_gradient_bound hm hα
  obtain ⟨C₂, hC₂, hc₂⟩ := newtonianPotential_hessian_bound hm hα
  obtain ⟨C₃, hC₃, hc₃⟩ := newtonianPotential_hessian_holder hm hα hα1
  let B := rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) 2
  have hB : 0 ≤ B := rieszBallMass_nonneg volume 2
  let C := B + 1 + C₁ + C₂ + C₃
  have hC : 0 < C := by dsimp [C]; positivity
  have h1 : C₁ ≤ C := by dsimp [C]; linarith
  have h2 : C₂ ≤ C := by dsimp [C]; linarith
  have h3 : C₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hfc hgc H U I hH hU hI hh hu hi
  let q := fun y => f y - g y
  have hq : ContDiff ℝ 2 q := hf.sub hg
  have hqc : HasCompactSupport q := hfc.sub hgc
  have hm1 : 1 ≤ m := by omega
  have hpot := newtonianPotential_sub hm1 f g hf.continuous hg.continuous hfc hgc
  have hgrad := newtonianPotential_derivative_sub hm1 f g hf hg hfc hgc
  have hhess := newtonianPotential_second_derivative_sub hm1 f g hf hg hfc hgc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have h := newtonianPotential_bound hm q (hq.continuous.integrable_of_hasCompactSupport hqc) hU hu hi x
    dsimp only [q] at h
    rw [hpot] at h
    apply h.trans
    have hU' := mul_nonneg (show 0 ≤ C - B by dsimp [C]; linarith) hU
    have hI' := mul_nonneg (show 0 ≤ C - 1 by dsimp [C]; linarith) hI
    nlinarith [mul_nonneg hC.le hH]
  · intro x
    have h := hc₁ q hq hqc H U I hH hU hI hh hu hi x
    dsimp only [q] at h
    rw [hgrad] at h
    exact h.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
  · intro x
    have h := hc₂ q hq hqc H U I hH hU hI hh hu hi x
    dsimp only [q] at h
    rw [hhess] at h
    exact h.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
  · intro x y
    have h := hc₃ q hq hqc H hH hh y x
    dsimp only [q] at h
    rw [hhess, hhess] at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hH) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
