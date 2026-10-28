import OAI.Analysis.PDE.Elliptic.Boundary.Third.ComposeTensor
import OAI.Analysis.Normed.Function.Holder.Boundary.ChartJets
import OAI.Analysis.Normed.Function.Holder.Boundary.HolderPullback
import OAI.Analysis.Normed.Function.Holder.Boundary.FixedHolder

/-! Uniform transport of the actual third derivative through a fixed
smooth boundary chart. The coefficient of the unknown third-jet norm is
independent of the solution. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I

local instance thirdChartFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdChartFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdChartSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdChartSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdChartThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdChartThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdChartFieldGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance thirdChartFieldSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance thirdChartFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance thirdChartFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance thirdChartFieldThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance thirdChartFieldThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [DecidableEq I] in
theorem exists_fixed_chart_jet_holders {S : Set E} (hS : IsCompact S)
    (hSc : Convex ℝ S) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {G : E → E} (hG : ContDiff ℝ 4 G) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
      (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
      (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ G x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ G) x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value L x = fderiv ℝ (fderiv ℝ (fderiv ℝ G)) x) := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ G)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ G))) := h₂.fderiv_right (by norm_num)
  obtain ⟨J, hJ⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hS hSc hdiam _
    (h₁.of_le (by norm_num)) hα hα1
  obtain ⟨K, hK⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hS hSc hdiam _
    (h₂.of_le (by norm_num)) hα hα1
  obtain ⟨L, hL⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hS hSc hdiam _ h₃ hα hα1
  exact ⟨J, K, L, hJ, hK, hL⟩

omit [DecidableEq I] in
theorem exists_chart_original_jet_holders
    {Ω K S : Set E} {hΩK : Ω ⊆ K} {α M : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hS : IsOpen S) (hSc : Convex ℝ S)
    {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (hM : 0 ≤ M) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ M)
    (hLip : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖G x-G y‖ ≤ M*‖x-y‖)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (u : E → ℝ)
    (hU₁ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x)
    (hU₂ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (hT : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) :
    ∃ (D : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] ℝ) α)
      (H : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] ℝ) α)
      (T' : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u (G x)) ∧
      (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) (G x)) ∧
      (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T' x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (G x)) ∧
      ‖D‖ ≤ max 1 M*‖U‖ ∧ ‖H‖ ≤ max 1 (M^α)*‖U‖ ∧ ‖T'‖ ≤ max 1 (M^α)*‖T‖ := by
  obtain ⟨D, hD, hDn⟩ := U.exists_chart_first_holder hS hSc hG hGK hGΩ hM hDG hα hα1 hdiam
  obtain ⟨H, hH, hHn⟩ := U.exists_chart_second_holder hG.continuous hGK hM hLip hα
  let g : closure S → K := fun x => ⟨G x, hGK x.property⟩
  have hg : Continuous g := (hG.continuous.comp continuous_subtype_val).subtype_mk _
  have hgLip (x y : closure S) : dist (g x) (g y) ≤ M*dist x y := by
    simpa only [g, Subtype.dist_eq, dist_eq_norm] using hLip x x.property y y.property
  obtain ⟨T', hT', hTn⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα T g hg hM hgLip
  exact ⟨D, H, T', fun x => (hD x).trans (hU₁ _), fun x => (hH x).trans (hU₂ _),
    fun x => (hT' x).trans (hT _), hDn, hHn, hTn⟩

theorem exists_uniform_chart_third_holder
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hS : IsOpen S) (hSc : Convex ℝ S)
    (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    {G : E → E} (hG : ContDiff ℝ 4 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ∀ u : E → ℝ, ContDiff ℝ 3 u →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)))) x) ∧
        ‖P‖ ≤ C*(‖U‖+‖T‖) := by
  obtain ⟨J, J₂, J₃, hJ, hJ₂, hJ₃⟩ := exists_fixed_chart_jet_holders
    hcompact hSc.closure hdiam hG hα hα1
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn
    (hG.continuous_fderiv (by norm_num)).continuousOn
  let M := max 1 M₀
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hDG (x) (hx : x ∈ closure S) : ‖fderiv ℝ G x‖ ≤ M :=
    (hM₀ x hx).trans (le_max_right _ _)
  have hLip (x) (hx : x ∈ closure S) (y) (hy : y ∈ closure S) :
      ‖G x-G y‖ ≤ M*‖x-y‖ := hSc.closure.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hG.differentiable (by norm_num) z) hDG hy hx
  let A := max 1 M
  let B := max 1 (M^α)
  let C := (Fintype.card I : ℝ)^3*(8*B*‖J‖^3+12*B*‖J₂‖*‖J‖+2*A*‖J₃‖)+1
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro U u hu hU₁ hU₂ T hT
  obtain ⟨D, H, T', hD, hH, hT', hDn, hHn, hTn⟩ := exists_chart_original_jet_holders
    U hS hSc (hG.of_le (by norm_num)) hGK hGΩ hM hDG hLip hα hα1 hdiam u hU₁ hU₂ T hT
  obtain ⟨P, hP, hPn⟩ := exists_composed_third_holder hα hu (hG.of_le (by norm_num))
    D H T' J J₂ J₃ hD hH hT' hJ hJ₂ hJ₃
  refine ⟨P, hP, hPn.trans ?_⟩
  exact third_chain_linear_bound (by positivity) (norm_nonneg J) (norm_nonneg J₂)
    (norm_nonneg J₃) hA hB (norm_nonneg U) (norm_nonneg T) hDn hHn hTn

end OAI.Analysis.PDE.Elliptic
