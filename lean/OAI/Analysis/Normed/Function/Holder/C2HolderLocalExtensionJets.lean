import OAI.Analysis.PDE.Dirichlet.C2HolderExtensionNonlinearJet

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance localExtensionJetsFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance localExtensionJetsFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance localExtensionJetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance localExtensionJetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Local agreement on a closed-domain patch suffices to identify both
derivative fields of an extension at every point of that patch. -/
theorem derivatives_of_local_C2_extension
    {Ω K O : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω) (hO : IsOpen O)
    (u : C2Holder (F := F) hΩK α)
    {g : E → F} (hg : ContDiff ℝ 2 g)
    (he : ∀ x : K, (x:E) ∈ O → g x = C2Holder.value u x) :
    ∀ x : K, (x:E) ∈ O → fderiv ℝ g x = C2Holder.firstDerivative u x ∧
      fderiv ℝ (fderiv ℝ g) x = C2Holder.secondDerivative u x := by
  have hdense : K ∩ O ⊆ closure (Ω ∩ O) := by
    intro x hx
    apply mem_closure_iff.mpr
    intro V hV hxV
    obtain ⟨y,hy,hyΩ⟩ := mem_closure_iff.mp (hKΩ hx.1)
      (V ∩ O) (hV.inter hO) ⟨hxV,hx.2⟩
    exact ⟨y,hy.1,hyΩ,hy.2⟩
  have hsub : Ω ∩ O ⊆ K ∩ O := fun _ hx => ⟨hΩK hx.1,hx.2⟩
  have hlocal (x : E) (hx : x ∈ Ω ∩ O) :
      g =ᶠ[𝓝 x] boundedZeroExtension (C2Holder.value u) := by
    filter_upwards [(hΩ.inter hO).mem_nhds hx] with y hy
    exact (he ⟨y,hΩK hy.1⟩ hy.2).trans
      (boundedZeroExtension_apply _ (hΩK hy.1)).symm
  have hfirst : EqOn (fderiv ℝ g) (boundedZeroExtension (C2Holder.firstDerivative u)) (Ω ∩ O) := by
    intro x hx
    exact (hlocal x hx).fderiv_eq.trans (C2Holder.hasFDerivAt_value_extension u hx.1).fderiv
  have hsecond : EqOn (fderiv ℝ (fderiv ℝ g))
      (boundedZeroExtension (C2Holder.secondDerivative u)) (Ω ∩ O) := by
    intro x hx
    have heq : fderiv ℝ g =ᶠ[𝓝 x] boundedZeroExtension (C2Holder.firstDerivative u) := by
      filter_upwards [(hΩ.inter hO).mem_nhds hx] with y hy
      exact hfirst hy
    exact heq.fderiv_eq.trans (C2Holder.hasFDerivAt_first_extension u hx.1).fderiv
  have hg₁ : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ g)) := hg₁.fderiv_right (by norm_num)
  have hfirstK := hfirst.of_subset_closure hg₁.continuous.continuousOn
    ((continuousOn_boundedZeroExtension (C2Holder.firstDerivative u)).mono inter_subset_left) hsub hdense
  have hsecondK := hsecond.of_subset_closure hg₂.continuous.continuousOn
    ((continuousOn_boundedZeroExtension (C2Holder.secondDerivative u)).mono inter_subset_left) hsub hdense
  intro x hx
  exact ⟨(hfirstK ⟨x.property,hx⟩).trans (boundedZeroExtension_apply _ x.property),
    (hsecondK ⟨x.property,hx⟩).trans (boundedZeroExtension_apply _ x.property)⟩

end OAI.Analysis.Normed.Function.Holder.C2Holder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

attribute [local instance] OAI.Analysis.PDE.Dirichlet.linearizedFirstGroup OAI.Analysis.PDE.Dirichlet.linearizedFirstSpace
  OAI.Analysis.PDE.Dirichlet.linearizedSecondGroup OAI.Analysis.PDE.Dirichlet.linearizedSecondSpace

variable {Z E W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Ω K O : Set E} {hΩK : Ω ⊆ K} {α : ℝ} {U : Set Z}

/-- Boundary identification for local joint extensions in arbitrary
linear coordinates. Agreement is required only on the spatial patch. -/
theorem parameterJetProjection_reindex_local_extension
    (e : W ≃L[ℝ] Z × E) (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω) (hO : IsOpen O)
    (u : Z → C2Holder (F := ℝ) hΩK α)
    {g : Z × E → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ U, ∀ x : K, (x:E) ∈ O → g (z,x) = OAI.Analysis.Normed.Function.Holder.C2Holder.value (u z) x)
    (w : W) (hz : (e w).1 ∈ U) (hx : (e w).2 ∈ K) (hxO : (e w).2 ∈ O) :
    OAI.Analysis.PDE.Dirichlet.parameterJetProjection (OAI.Analysis.PDE.Dirichlet.reindexParameterProjection e) (OAI.Analysis.PDE.Dirichlet.reindexSpatialProjection e)
      (OAI.Analysis.PDE.Dirichlet.reindexSpatialInclusion e) (OAI.Analysis.PDE.Dirichlet.nonlinearTwoJet (fun y => g (e y)) w) =
      ((e w).1,OAI.Analysis.PDE.Dirichlet.storedNonlinearTwoJet (u (e w).1) ⟨(e w).2,hx⟩) := by
  rw [OAI.Analysis.PDE.Dirichlet.parameterJetProjection_reindex_twoJet e hg w]
  obtain ⟨hD,hH⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.derivatives_of_local_C2_extension hΩ hKΩ hO (u (e w).1)
    (hg.comp (contDiff_const.prodMk contDiff_id)) (he (e w).1 hz) ⟨(e w).2,hx⟩ hxO
  simp only [Function.comp_def,id_eq] at hD hH
  simp only [OAI.Analysis.PDE.Dirichlet.nonlinearTwoJet,OAI.Analysis.PDE.Dirichlet.storedNonlinearTwoJet,hD,hH]

end OAI.Analysis.PDE.Dirichlet
