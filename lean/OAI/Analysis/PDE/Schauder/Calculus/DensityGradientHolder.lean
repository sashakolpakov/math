import OAI.Analysis.PDE.Dirichlet.DensityPath
import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetBounds

noncomputable section
open Set Module
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_densityPath (f g : E → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (t : ℝ) (x : E) :
    fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath f g t) x = (1-t) • fderiv ℝ f x+t • fderiv ℝ g x := by
  exact (((hf x).hasFDerivAt.const_smul (1-t)).add
    ((hg x).hasFDerivAt.const_smul t)).fderiv

theorem norm_affine_segment_le_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x y : F} {C D t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ D) : ‖(1-t) • x+t • y‖ ≤ C+D := by
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  calc
    _ ≤ ‖(1-t) • x‖+‖t • y‖ := norm_add_le _ _
    _ = (1-t)*‖x‖+t*‖y‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht',abs_of_nonneg ht.1]
    _ ≤ (1-t)*C+t*D := add_le_add
      (mul_le_mul_of_nonneg_left hx ht') (mul_le_mul_of_nonneg_left hy ht.1)
    _ ≤ C+D := by nlinarith [mul_nonneg ht.1 hC,mul_nonneg ht' hD]

/-- The differentiated density path has a single C^α bound on the whole
periodic domain, derived from its two fixed C² endpoints. -/
theorem densityPath_uniform_gradient_holder_lattice [ProperSpace E]
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) (hgp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B > 0, ∀ t ∈ Icc (0:ℝ) 1,
      (∀ x, r x ≤ 0 → ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath f g t) x‖ ≤ B) ∧
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
        ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath f g t) x-fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath f g t) y‖ ≤ B*dist x y^α) := by
  obtain ⟨C,hC,hCn,hCh⟩ := OAI.Analysis.PDE.Dirichlet.periodic_smooth_jet_holder_bound e b hK hr hrp hbounded
    (fderiv ℝ f) (hf.fderiv_right (by norm_num)) hfp.fderiv hα hα1
  obtain ⟨D,hD,hDn,hDh⟩ := OAI.Analysis.PDE.Dirichlet.periodic_smooth_jet_holder_bound e b hK hr hrp hbounded
    (fderiv ℝ g) (hg.fderiv_right (by norm_num)) hgp.fderiv hα hα1
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro t ht
  constructor
  · intro x hx
    rw [fderiv_densityPath f g (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
    exact norm_affine_segment_le_sum ht hC.le hD.le (hCn x hx) (hDn x hx)
  · intro x hx y hy
    rw [fderiv_densityPath f g (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)),
      fderiv_densityPath f g (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
    have heq : (1-t) • fderiv ℝ f x+t • fderiv ℝ g x-
        ((1-t) • fderiv ℝ f y+t • fderiv ℝ g y) =
        (1-t) • (fderiv ℝ f x-fderiv ℝ f y)+t • (fderiv ℝ g x-fderiv ℝ g y) := by module
    rw [heq]
    have hp := Real.rpow_nonneg (show 0 ≤ dist x y from dist_nonneg) α
    exact (norm_affine_segment_le_sum ht (mul_nonneg hC.le hp) (mul_nonneg hD.le hp)
      (hCh x hx y hy) (hDh x hx y hy)).trans_eq (by ring)

end OAI.Analysis.PDE.Schauder
