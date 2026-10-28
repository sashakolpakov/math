import OAI.Analysis.PDE.Elliptic.Boundary.Third.ComposeTensor
import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder

/-! Returning a third-order boundary estimate to physical coordinates,
with constants independent of the solution. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I

local instance inverseThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseThirdFieldGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance inverseThirdFieldSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance inverseThirdFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseThirdFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseThirdFieldThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseThirdFieldThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [DecidableEq I] in
theorem exists_fixed_compact_chart_jets {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 4 P) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
      (J₂ : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
      (J₃ : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ P x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J₂ x = fderiv ℝ (fderiv ℝ P) x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J₃ x = fderiv ℝ (fderiv ℝ (fderiv ℝ P)) x) := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ P) := hP.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ P)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ P))) := h₂.fderiv_right (by norm_num)
  obtain ⟨J, hJ⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ (h₁.of_le (by norm_num)) hα hα1
  obtain ⟨J₂, hJ₂⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ (h₂.of_le (by norm_num)) hα hα1
  obtain ⟨J₃, hJ₃⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ h₃ hα hα1
  exact ⟨J, J₂, J₃, hJ, hJ₂, hJ₃⟩

omit [DecidableEq I] in
theorem exists_pulledback_jet_holders {S K : Set E} {α L N M : ℝ}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (p : S → K) (hp : Continuous p) (hpl : ∀ x y, dist (p x) (p y) ≤ L*dist x y)
    (v : E → ℝ) (hv : ContDiff ℝ 3 v) (hvb : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn v K α N)
    (hvn : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ M)
    (hvh : ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y‖ ≤ M*‖x-y‖^α) :
    ∃ (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
      (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
      (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ v (p x)) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ v) (p x)) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ v)) (p x)) ∧
      ‖D‖ ≤ max 1 (L^α)*N ∧ ‖H‖ ≤ max 1 (L^α)*N ∧ ‖T‖ ≤ max 1 (L^α)*M := by
  obtain ⟨D, H, hD, hH, hDn, hHn⟩ := OAI.Analysis.Normed.Function.Holder.exists_lower_jet_holder hα hN v (hv.of_le (by norm_num)) hvb
  have hvc : Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) :=
    continuous_third_composition hv (contDiff_id : ContDiff ℝ 3 (id : E → E))
  obtain ⟨T, hT, hTn⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_field_of_bounds hα hM _ hvc.continuousOn hvn hvh
  obtain ⟨D', hD', hD'n⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα D p hp hL hpl
  obtain ⟨H', hH', hH'n⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα H p hp hL hpl
  obtain ⟨T', hT', hT'n⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα T p hp hL hpl
  have hB : 0 ≤ max 1 (L^α) := le_trans (by norm_num) (le_max_left _ _)
  exact ⟨D', H', T', fun x => (hD' x).trans (hD _), fun x => (hH' x).trans (hH _),
    fun x => (hT' x).trans (hT _),
    hD'n.trans (mul_le_mul_of_nonneg_left hDn hB),
    hH'n.trans (mul_le_mul_of_nonneg_left hHn hB),
    hT'n.trans (mul_le_mul_of_nonneg_left hTn hB)⟩

theorem exists_inverse_chart_third_holder {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 4 P) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ K : Set E, MapsTo P S K → ∀ v u : E → ℝ, ContDiff ℝ 3 v →
      (∀ x ∈ S, (fun y => v (P y)) =ᶠ[𝓝 x] u) →
      ∀ N M : ℝ, 0 ≤ N → 0 ≤ M → OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn v K α N →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ M) →
      (∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y‖ ≤
          M*‖x-y‖^α) →
      ∃ U : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) ∧
        ‖U‖ ≤ C*(N+M) := by
  obtain ⟨J, J₂, J₃, hJ, hJ₂, hJ₃⟩ := exists_fixed_compact_chart_jets hS hP hα hα1
  obtain ⟨L, hL, _, hLip⟩ := OAI.Analysis.PDE.Dirichlet.smooth_jet_compact_holder_bound P (hP.of_le (by norm_num))
    hS (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  let B := max 1 (L^α)
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let C := (Fintype.card I : ℝ)^3*(8*B*‖J‖^3+12*B*‖J₂‖*‖J‖+2*B*‖J₃‖)+1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro K hPK v u hv heq N M hN hM hvb hvn hvh
  let p : S → K := fun x => ⟨P x, hPK x.property⟩
  have hp : Continuous p := (hP.continuous.comp continuous_subtype_val).subtype_mk _
  have hpl (x y : S) : dist (p x) (p y) ≤ L*dist x y := by
    simpa only [p, Subtype.dist_eq, dist_eq_norm, Real.rpow_one] using hLip x x.property y y.property
  obtain ⟨D', H', T', hD', hH', hT', hD'n, hH'n, hT'n⟩ :=
    exists_pulledback_jet_holders hα hL.le hN hM p hp hpl v hv hvb hvn hvh
  obtain ⟨U, hU, hUn⟩ := exists_composed_third_holder hα hv (hP.of_le (by norm_num))
    D' H' T' J J₂ J₃ hD' hH' hT' hJ hJ₂ hJ₃
  refine ⟨U, ?_, hUn.trans ?_⟩
  · intro x
    exact (hU x).trans (((heq x x.property).fderiv.fderiv).fderiv_eq)
  · exact third_chain_linear_bound (by positivity) (norm_nonneg J) (norm_nonneg J₂)
      (norm_nonneg J₃) hB hB hN hM hD'n hH'n hT'n

end OAI.Analysis.PDE.Elliptic
