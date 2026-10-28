import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentChartDerivatives
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationJets
import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.SmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance doubleTangent1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance doubleTangent1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance doubleTangent2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance doubleTangent2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A closed C²,α jet of the genuine twice-tangential derivative gives
the flat-coordinate second-derivative Hölder field needed for normal
reconstruction. The transport constant depends only on the fixed chart. -/
theorem exists_double_tangent_chart_holder
    {G P : E → E} (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    {S Ω K : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hGK : MapsTo G S K) {hΩK : Ω ⊆ K} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ (u : E → ℝ) (T W : E → E),
      ContDiff ℝ 4 u → ContDiff ℝ 3 T → ContDiff ℝ 2 W →
      ∀ v w : E,
      (∀ z ∈ S, (fun y => P (G y)) =ᶠ[𝓝 z] id) →
      (∀ z ∈ S, T =ᶠ[𝓝 (G z)] chartTangentField G P v) →
      (∀ z ∈ S, W =ᶠ[𝓝 (G z)] chartTangentField G P w) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = fieldDerivative (fieldDerivative u T) W x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ (fieldDerivative (fieldDerivative u T) W) x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
        fderiv ℝ (fderiv ℝ (fieldDerivative (fieldDerivative u T) W)) x) →
      ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x =
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ G) v) w)) x) ∧
        ‖H‖ ≤ C*‖U‖ := by
  obtain ⟨C,hC,hchart⟩ := OAI.Analysis.PDE.Dirichlet.exists_chart_jet_holder_bound G hG hS hSc hGK
    (hΩK := hΩK) hα hα1
  refine ⟨C,hC,?_⟩
  intro u T W hu hT hW v w hinv hTg hWg U hU₀ hU₁ hU₂
  let q := fieldDerivative (fieldDerivative u T) W
  have hq₁ : ContDiff ℝ 3 (fieldDerivative u T) := contDiff_fieldDerivative hu hT (by norm_num)
  have hq : ContDiff ℝ 2 q := contDiff_fieldDerivative hq₁ hW (by norm_num)
  have hb := hchart q hq U hU₀ hU₁ hU₂
  obtain ⟨D,H,_,hH,_,hHn⟩ := OAI.Analysis.Normed.Function.Holder.exists_lower_jet_holder hα (mul_nonneg hC.le (norm_nonneg U))
    (q ∘ G) (hq.comp (hG.of_le (by norm_num))) hb
  refine ⟨H,?_,hHn⟩
  intro x
  have he := OAI.Analysis.Calculus.SmoothExtension.twice_fieldDerivative_chart_germ hG hP (hu.of_le (by norm_num)) v w (x : E)
    (hinv x x.property) (hTg x x.property) (hWg x x.property)
  have huG : ContDiff ℝ 2 (u ∘ G) := (hu.of_le (by norm_num)).comp (hG.of_le (by norm_num))
  have he' : (q ∘ G) =ᶠ[𝓝 (x : E)] OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ G) v) w := by
    filter_upwards [he] with y hy
    change fieldDerivative (fieldDerivative u T) W (G y) = _
    rw [OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice huG]
    exact hy
  exact (hH x).trans he'.fderiv.fderiv_eq

end OAI.Analysis.PDE.Elliptic
