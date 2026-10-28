import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ClosedExtraction
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.GeometricFamilies

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z X Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Every mixed parameter derivative commutes with continuous linear
evaluation, including evaluation of the actual stored closed-domain jet. -/
theorem iteratedFDeriv_clm_family (L : X →L[ℝ] Y) {U : Z → X} {t : Z}
    (hU : ContDiffAt ℝ ∞ U t) (N : ℕ) (v : Fin N → Z) :
    iteratedFDeriv ℝ N (fun s ↦ L (U s)) t v =
      L (iteratedFDeriv ℝ N U t v) := by
  exact congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ Z) Y ↦ A v)
    (L.iteratedFDeriv_comp_left hU (i := N) (by simp))

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {r : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}

local instance mixedParamFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance mixedParamFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance mixedParamSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance mixedParamSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance mixedParamHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance mixedParamHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem value_iteratedFDeriv_family {U : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α}
    {t : Z} (hU : ContDiffAt ℝ ∞ U t) (N : ℕ) (v : Fin N → Z)
    (x : {x | r x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (iteratedFDeriv ℝ N U t v) x =
      iteratedFDeriv ℝ N (fun s ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x) t v := by
  exact (ParameterDeformation.iteratedFDeriv_clm_family (jetValueEvaluation x) hU N v).symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Mixed tangential parameter derivatives are represented by actual
C²,α jets. No prior high spatial differentiability of f is assumed. -/
theorem exists_mixed_tangent_jet_of_parameter_family
    {U : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α} (hU : ContDiffAt ℝ ∞ U 0)
    {S : Set V} (G : V → E) (hG : MapsTo G S {x | r x ≤ 0})
    (f : V → ℝ) (A : Z →L[ℝ] V)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hG hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z+A t))
    (N : ℕ) (v : Fin N → Z) :
    ∃ W : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ∀ z (hz : z ∈ S),
      OAI.Analysis.Normed.Function.Holder.C2Holder.value W ⟨G z,hG hz⟩ =
        iteratedFDeriv ℝ N (fun t : Z ↦ f (z+A t)) 0 v := by
  refine ⟨iteratedFDeriv ℝ N U 0 v,?_⟩
  intro z hz
  rw [ParameterDeformation.value_iteratedFDeriv_family hU]
  exact congrArg (fun B : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ Z) ℝ ↦ B v)
    (((he z hz).iteratedFDeriv ℝ N).eq_of_nhds)

omit [Nontrivial E] in
theorem mixed_tangent_contDiffOn_of_parameter_family
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {U : Z → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α} (hU : ContDiffAt ℝ ∞ U 0)
    {S : Set V} {G : V → E} (hG : ContDiffOn ℝ 2 G S)
    (hGS : MapsTo G S {x | r x ≤ 0}) {f : V → ℝ} (A : Z →L[ℝ] V)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z+A t))
    (N : ℕ) (v : Fin N → Z) :
    ContDiffOn ℝ 2 (fun z ↦ iteratedFDeriv ℝ N (fun t : Z ↦ f (z+A t)) 0 v) S := by
  obtain ⟨W,hW⟩ := ParameterDeformation.exists_mixed_tangent_jet_of_parameter_family hU G hGS f A he N v
  exact closed_tangent_contDiffOn_of_jet hr hreg hG hGS W hW

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
