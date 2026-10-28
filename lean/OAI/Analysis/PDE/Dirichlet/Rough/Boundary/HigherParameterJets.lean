import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ClosedExtraction
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

section Evaluation
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Every finite parameter derivative commutes with a bounded evaluation
map. This preserves the full smooth-parameter output of the implicit
function theorem, rather than truncating it after two derivatives. -/
theorem iteratedDeriv_clm_curve (L : X →L[ℝ] Y) {U : ℝ → X} {t : ℝ}
    (hU : ContDiffAt ℝ ∞ U t) (N : ℕ) :
    iteratedDeriv N (fun s ↦ L (U s)) t = L (iteratedDeriv N U t) := by
  have h := L.iteratedFDeriv_comp_left hU (i := N) (by simp)
  exact congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ ℝ) Y ↦
    A (fun _ ↦ 1)) h

end Evaluation

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {r : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}

local instance higherParamFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance higherParamFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance higherParamSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance higherParamSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance higherParamHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance higherParamHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem value_iteratedDeriv_curve {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α}
    {t : ℝ} (hU : ContDiffAt ℝ ∞ U t) (N : ℕ) (x : {x | r x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (iteratedDeriv N U t) x =
      iteratedDeriv N (fun s ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x) t := by
  exact (iteratedDeriv_clm_curve (jetValueEvaluation x) hU N).symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The N-th tangential derivative is represented by an actual C²,α jet
for every N. No N-th spatial differentiability assumption on f is used:
the line derivative exists and is obtained from the smooth Banach curve. -/
theorem exists_higher_tangent_jet_of_parameter_curve
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α} (hU : ContDiffAt ℝ ∞ U 0)
    {S : Set V} (G : V → E) (hG : MapsTo G S {x | r x ≤ 0})
    (f : V → ℝ) (v : V)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hG hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z+t • v))
    (N : ℕ) :
    ∃ W : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ∀ z (hz : z ∈ S),
      OAI.Analysis.Normed.Function.Holder.C2Holder.value W ⟨G z,hG hz⟩ = iteratedDeriv N (fun t : ℝ ↦ f (z+t • v)) 0 := by
  refine ⟨iteratedDeriv N U 0,?_⟩
  intro z hz
  rw [value_iteratedDeriv_curve hU]
  exact (he z hz).iteratedDeriv_eq N

omit [Nontrivial E] in
/-- All finite pure tangential derivatives have two continuous spatial
derivatives up to the boundary, with the same physical closed-domain
interpretation as the original C²,α jet. -/
theorem higher_tangent_contDiffOn_of_parameter_curve
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α} (hU : ContDiffAt ℝ ∞ U 0)
    {S : Set V} {G : V → E} (hG : ContDiffOn ℝ 2 G S)
    (hGS : MapsTo G S {x | r x ≤ 0}) {f : V → ℝ} (v : V)
    (he : ∀ z (hz : z ∈ S),
      (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz⟩) =ᶠ[𝓝 0] fun t ↦ f (z+t • v))
    (N : ℕ) : ContDiffOn ℝ 2 (fun z ↦ iteratedDeriv N (fun t : ℝ ↦ f (z+t • v)) 0) S := by
  obtain ⟨W,hW⟩ := exists_higher_tangent_jet_of_parameter_curve hU G hGS f v he N
  exact closed_tangent_contDiffOn_of_jet hr hreg hG hGS W hW

end OAI.Analysis.PDE.Dirichlet
