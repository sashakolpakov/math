import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet
import OAI.Analysis.PDE.Schauder.Calculus.DensityGradientHolder
import OAI.Analysis.Normed.Function.Holder.Boundary.LogCoefficient

noncomputable section
open Set Module
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
local instance logDensityDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance logDensityDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

/-- The positive density path has a uniformly bounded actual logarithmic
gradient in the same Hölder exponent, including its closed boundary. -/
theorem densityPath_uniform_log_gradient_holder
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) (hgp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g)
    (hfpos : ∀ x, r x ≤ 0 → 0 < f x) (hgpos : ∀ x, r x ≤ 0 → 0 < g x)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1,
      ∃ W : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α, ‖W‖ ≤ C ∧
        ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value W x =
          (OAI.Analysis.PDE.Dirichlet.densityPath f g t x)⁻¹ • fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath f g t) x := by
  obtain ⟨p₀,hp₀⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodic_holder_field e b hK hr hrp hbounded f
    (hf.of_le (by norm_num)) hfp hα hα1
  obtain ⟨p₁,hp₁⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodic_holder_field e b hK hr hrp hbounded g
    (hg.of_le (by norm_num)) hgp hα hα1
  obtain ⟨q₀,hq₀⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodic_holder_field e b hK hr hrp hbounded (fderiv ℝ f)
    (hf.fderiv_right (by norm_num)) hfp.fderiv hα hα1
  obtain ⟨q₁,hq₁⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodic_holder_field e b hK hr hrp hbounded (fderiv ℝ g)
    (hg.fderiv_right (by norm_num)) hgp.fderiv hα hα1
  obtain ⟨μ,_,_,hμ,_,_,hbound⟩ := OAI.Analysis.PDE.Dirichlet.densityPath_uniform_bounds_lattice e b hK hr hrp
    hbounded hne hf hg hfp hgp hfpos hgpos
  let L : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
  let C := 2*‖L‖*(μ⁻¹+(μ*μ)⁻¹*(‖p₀‖+‖p₁‖))*(‖q₀‖+‖q₁‖)+1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro t ht
  let p := (1-t) • p₀+t • p₁
  let q := (1-t) • q₀+t • q₁
  have hp (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value p x = OAI.Analysis.PDE.Dirichlet.densityPath f g t x := by
    change (1-t)*OAI.Analysis.Normed.Function.Holder.HolderMap.value p₀ x+t*OAI.Analysis.Normed.Function.Holder.HolderMap.value p₁ x = _
    rw [hp₀,hp₁]; rfl
  have hq (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value q x = fderiv ℝ (OAI.Analysis.PDE.Dirichlet.densityPath f g t) x := by
    change (1-t) • OAI.Analysis.Normed.Function.Holder.HolderMap.value q₀ x+t • OAI.Analysis.Normed.Function.Holder.HolderMap.value q₁ x = _
    rw [hq₀,hq₁,fderiv_densityPath f g (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  have hpn : ‖p‖ ≤ ‖p₀‖+‖p₁‖ := norm_affine_segment_le_sum ht
    (norm_nonneg _) (norm_nonneg _) le_rfl le_rfl
  have hqn : ‖q‖ ≤ ‖q₀‖+‖q₁‖ := norm_affine_segment_le_sum ht
    (norm_nonneg _) (norm_nonneg _) le_rfl le_rfl
  obtain ⟨pi,hpi,hpin⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_positive_reciprocal hα p hμ (fun x => by
    rw [hp]; exact (hbound t ht x x.property).1)
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα L pi q, ?_, ?_⟩
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_bilinear_le hα L pi q).trans
    have hin : ‖pi‖ ≤ μ⁻¹+(μ*μ)⁻¹*(‖p₀‖+‖p₁‖) := hpin.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpn (by positivity)))
    dsimp only [C]
    apply le_trans _ (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))
    gcongr
  · intro x
    rw [OAI.Analysis.Normed.Function.Holder.HolderMap.value_bilinear,hpi,hp,hq]
    rfl

end OAI.Analysis.PDE.Schauder
