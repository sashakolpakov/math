import OAI.Analysis.PDE.Schauder.Calculus.DensityGradientHolder
import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet

noncomputable section
open Set Module
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance densityFourthFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance densityFourthFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance densityFourthSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance densityFourthSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem second_fderiv_densityPath (f g : E → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (densityPath f g t)) x =
      (1-t) • fderiv ℝ (fderiv ℝ f) x+t • fderiv ℝ (fderiv ℝ g) x := by
  have heq : fderiv ℝ (densityPath f g t) =
      fun y => (1-t) • fderiv ℝ f y+t • fderiv ℝ g y :=
    funext (OAI.Analysis.PDE.Schauder.fderiv_densityPath f g (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) t)
  rw [heq]
  exact ((((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt.const_smul
    (1-t)).add (((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt.const_smul t)).fderiv

/-- Uniform Hölder Hessian fields for the whole affine density path.
Only the two fixed endpoints, not the path parameter, choose the constant. -/
theorem exists_densityPath_hessian_holder [ProperSpace E]
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f g : E → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (hfp : LatticePeriodic e b f) (hgp : LatticePeriodic e b g)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ (densityPath f g t)) x) ∧ ‖H‖ ≤ C := by
  obtain ⟨H0,hH0⟩ := exists_periodic_holder_field e b hK hr hrp hbounded
    (fderiv ℝ (fderiv ℝ f)) ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num))
    hfp.fderiv.fderiv hα hα1
  obtain ⟨H1,hH1⟩ := exists_periodic_holder_field e b hK hr hrp hbounded
    (fderiv ℝ (fderiv ℝ g)) ((hg.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num))
    hgp.fderiv.fderiv hα hα1
  refine ⟨1+‖H0‖+‖H1‖,by positivity,?_⟩
  intro t ht
  refine ⟨(1-t) • H0+t • H1,?_,?_⟩
  · intro x
    simp only [OAI.Analysis.Normed.Function.Holder.HolderMap.value_add,OAI.Analysis.Normed.Function.Holder.HolderMap.value_smul,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply,hH0,hH1]
    exact (second_fderiv_densityPath f g (hf.of_le (by norm_num))
      (hg.of_le (by norm_num)) t x).symm
  · exact (OAI.Analysis.PDE.Schauder.norm_affine_segment_le_sum ht (norm_nonneg H0) (norm_nonneg H1) le_rfl le_rfl).trans
      (by linarith)

end OAI.Analysis.PDE.Dirichlet
