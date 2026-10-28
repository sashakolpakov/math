import OAI.Analysis.PDE.Elliptic.Boundary.SubtractedChartHolder
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.RemainderJets

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I A : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance pathLowerAssembly1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathLowerAssembly1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathLowerAssembly2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathLowerAssembly2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathLowerAssembly3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathLowerAssembly3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Uniform lower chart bounds assembled from actual second and third
jet fields. This lemma is independent of the nonlinear equation. -/
theorem uniform_subtracted_chart_jets_of_fields
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hS : IsOpen S) (hSc : Convex ℝ S)
    (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    {G : E → E} (hG : ContDiff ℝ 4 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (B : E → ℝ) (hB : ContDiff ℝ 4 B)
    {α R₂ R₃ : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR₂ : 0 ≤ R₂) (hR₃ : 0 ≤ R₃)
    (u : A → E → ℝ) (hu : ∀ a, ContDiff ℝ 3 (u a))
    (U : A → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hUn : ∀ a, ‖U a‖ ≤ R₂)
    (hU₀ : ∀ a (x : K), OAI.Analysis.Normed.Function.Holder.C2Holder.value (U a) x = u a x)
    (hU₁ : ∀ a (x : K), OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (U a) x = fderiv ℝ (u a) x)
    (hU₂ : ∀ a (x : K), OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (U a) x = fderiv ℝ (fderiv ℝ (u a)) x)
    (T : A → OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hTn : ∀ a, ‖T a‖ ≤ R₃)
    (hT : ∀ a (x : K), OAI.Analysis.Normed.Function.Holder.HolderMap.value (T a) x = fderiv ℝ (fderiv ℝ (fderiv ℝ (u a))) x) :
    ∃ N > 0, ∀ a,
      OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn (fun z => u a (G z)-B (G z)) (closure S) α N ∧
      ∃ D : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => u a (G z)-B (G z)))) x) ∧ ‖D‖ ≤ N := by
  obtain ⟨V,hV,hlower⟩ := exists_chart_remainder_jet_bound G
    (hG.of_le (by norm_num)) B (hB.of_le (by norm_num)) hcompact hSc.closure hGK
    (hΩK := hΩK) hα hα1 hR₂
  obtain ⟨C,hC,hchart⟩ := exists_uniform_subtracted_chart_third_holder hΩK hS hSc
    hcompact hdiam hG hGK hGΩ B hB hα hα1
  let N := V+C*(1+R₂+R₃)+1
  have hN : 0 < N := by dsimp [N]; positivity
  have hVN : V ≤ N := by
    have ht : 0 ≤ C*(1+R₂+R₃) := by positivity
    dsimp [N]; linarith
  have hCN : C*(1+R₂+R₃) ≤ N := by dsimp [N]; linarith
  refine ⟨N,hN,?_⟩
  intro a
  have hlo := hlower (u a) ((hu a).of_le (by norm_num)) (U a) (hUn a)
    (hU₀ a) (hU₁ a) (hU₂ a)
  refine ⟨c2JetHolderBoundsOn_mono hlo hVN,?_⟩
  obtain ⟨D,hD,hDn⟩ := hchart (U a) (u a) (hu a) (hU₁ a) (hU₂ a) (T a) (hT a)
  refine ⟨D,hD,hDn.trans (le_trans ?_ hCN)⟩
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl (hUn a)) (hTn a)) hC.le

end OAI.Analysis.PDE.Elliptic
