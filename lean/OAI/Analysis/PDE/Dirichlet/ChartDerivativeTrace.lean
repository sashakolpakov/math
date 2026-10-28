import OAI.Analysis.PDE.Dirichlet.Closed.DerivativeTrace

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous interior derivative data extend to the physical boundary
through an actual smooth chart. The physical domain need not be convex. -/
theorem hasFDerivWithinAt_of_chart_trace
    {Ω D S K : Set E} (hS : IsOpen S) (hc : Convex ℝ S)
    {G P : E → E} (hG : ContDiff ℝ 1 G) (hP : ContDiff ℝ 1 P)
    (hGD : MapsTo G (closure S) D) (hGΩ : MapsTo G S Ω)
    (hPK : MapsTo P K (closure S))
    {a : E} (hPa : P a ∈ closure S) (hK : K ∈ 𝓝[D] a)
    (hinv : (fun x => G (P x)) =ᶠ[𝓝 a] id)
    {f : E → F} {A : E → E →L[ℝ] F}
    (hf : ContinuousOn f D) (hA : ContinuousOn A D)
    (hd : ∀ x ∈ Ω, HasFDerivAt f (A x) x) :
    HasFDerivWithinAt f (A a) D a := by
  let B := fun z => (A (G z)).comp (fderiv ℝ G z)
  have hfG : ContinuousOn (fun z => f (G z)) (closure S) :=
    hf.comp hG.continuous.continuousOn hGD
  have hB : ContinuousOn B (closure S) :=
    (hA.comp hG.continuous.continuousOn hGD).clm_comp
      (hG.continuous_fderiv (by norm_num)).continuousOn
  have hdG : ∀ z ∈ S, HasFDerivAt (fun y => f (G y)) (B z) z := by
    intro z hz
    exact (hd (G z) (hGΩ hz)).comp z
      ((hG.differentiable (by norm_num) z).hasFDerivAt)
  have hclosed := hasFDerivWithinAt_closure_of_continuous_trace hS hc hfG hB hdG hPa
  have hcomposed := hclosed.comp a
    ((hP.differentiable (by norm_num) a).hasFDerivAt.hasFDerivWithinAt) hPK
  have hGP : G (P a) = a := hinv.eq_of_nhds
  have hlinear : (fderiv ℝ G (P a)).comp (fderiv ℝ P a) =
      ContinuousLinearMap.id ℝ E := by
    have hh := hinv.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (G ∘ P) a = fderiv ℝ id a at hh
    rw [((hG.differentiable (by norm_num) (P a)).hasFDerivAt.comp a
      ((hP.differentiable (by norm_num) a).hasFDerivAt)).fderiv, fderiv_id] at hh
    exact hh
  have hder : (B (P a)).comp (fderiv ℝ P a) = A a := by
    dsimp [B]
    rw [ContinuousLinearMap.comp_assoc, hlinear, ContinuousLinearMap.comp_id, hGP]
  rw [hder] at hcomposed
  have he : (fun x => f (G (P x))) =ᶠ[𝓝 a] f := hinv.fun_comp f
  exact (hcomposed.congr_of_eventuallyEq
    (he.symm.filter_mono nhdsWithin_le_nhds) he.symm.eq_of_nhds).mono_of_mem_nhdsWithin hK

end OAI.Analysis.PDE.Dirichlet
