import OAI.Analysis.PDE.Dirichlet.Rough.Joint.ClassicalJets
import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {Z E X W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem derivatives_comp_eq_of_twoJet
    {f g : E → ℝ} {G : X → E} {x : X}
    (hf : ContDiffAt ℝ 2 f (G x)) (hg : ContDiffAt ℝ 2 g (G x))
    (hG : ContDiffAt ℝ 2 G x)
    (hD : fderiv ℝ f (G x) = fderiv ℝ g (G x))
    (hH : fderiv ℝ (fderiv ℝ f) (G x) = fderiv ℝ (fderiv ℝ g) (G x)) :
    fderiv ℝ (fun y => f (G y)) x = fderiv ℝ (fun y => g (G y)) x ∧
      fderiv ℝ (fderiv ℝ (fun y => f (G y))) x =
        fderiv ℝ (fderiv ℝ (fun y => g (G y))) x := by
  constructor
  · rw [fderiv_fun_comp x (hf.differentiableAt (by norm_num))
      (hG.differentiableAt (by norm_num)),
      fderiv_fun_comp x (hg.differentiableAt (by norm_num))
      (hG.differentiableAt (by norm_num)),hD]
  · ext v w
    rw [OAI.Analysis.PDE.Elliptic.second_fderiv_comp hf hG,OAI.Analysis.PDE.Elliptic.second_fderiv_comp hg hG,hD,hH]

/-- The joint extension has the true spatial chart jets of the chosen
classical slices, including on the boundary. The chosen family need not
already have any parameter regularity. -/
theorem parameterJetProjection_of_classical_chart
    (e : W ≃L[ℝ] Z × X) {Ω K : Set E} {S : Set Z}
    (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    {F : Z × E → ℝ}
    (hF : ∀ z ∈ S, ∀ x ∈ K, ContDiffAt ℝ 2 (fun y => F (z,y)) x)
    {g : Z × E → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ S, ∀ x ∈ K, g (z,x) = F (z,x))
    {G : X → E} (hG : ContDiff ℝ 2 G)
    (w : W) (hz : (e w).1 ∈ S) (hx : G (e w).2 ∈ K) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e)
      (nonlinearTwoJet (fun y => g ((e y).1,G (e y).2)) w) =
        ((e w).1,nonlinearTwoJet (fun x => F ((e w).1,G x)) (e w).2) := by
  have hprod : ContDiff ℝ 2 (fun p : Z × X => g (p.1,G p.2)) :=
    hg.comp (contDiff_fst.prodMk (hG.comp contDiff_snd))
  have hp := parameterJetProjection_reindex_twoJet e hprod w
  have hslice : ContDiff ℝ 2 (fun x : E => g ((e w).1,x)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hD,hH⟩ := derivatives_eq_on_dense_closed_domain_at hΩ hΩK hKΩ
    (fun _ _ => hslice.contDiffAt) (hF (e w).1 hz) (he (e w).1 hz) (G (e w).2) hx
  obtain ⟨hD',hH'⟩ := derivatives_comp_eq_of_twoJet
    hslice.contDiffAt (hF (e w).1 hz _ hx) hG.contDiffAt hD hH
  simpa only [nonlinearTwoJet,hD',hH'] using hp

end OAI.Analysis.PDE.Dirichlet
