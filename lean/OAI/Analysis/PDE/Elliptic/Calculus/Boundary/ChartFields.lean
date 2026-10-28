import OAI.Analysis.PDE.Elliptic.DirichletChartHolderFields
import OAI.Analysis.Normed.Function.Holder.Boundary.HolderPullback
import OAI.Analysis.Normed.Function.Holder.Boundary.FixedHolder

/-! Chart coefficient fields from an actual Hölder coefficient on the
physical closed domain. No continuity off that domain is assumed. -/

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance sourceChartEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance sourceChartEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance sourceChartSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance sourceChartSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem exists_holder_on_of_bounds {S : Set E} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M) (f : S → F) (hf : Continuous f)
    (hn : ∀ x, ‖f x‖ ≤ M) (hh : ∀ x y, ‖f x-f y‖ ≤ M*dist x y^α) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap S F α, (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = f x) ∧ ‖H‖ ≤ M := by
  let b : S →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup f hf M hn
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b hh, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα b hM hh).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hf hM hn) le_rfl)

theorem exists_chart_holder_fields_on
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P)
    {S K : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hGK : MapsTo G S K)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ (A : E → E →L[ℝ] E)
      (a : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α),
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = A x) →
      ∃ (B : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α) (V : OAI.Analysis.Normed.Function.Holder.HolderMap S E α),
        ‖B‖ ≤ C*‖a‖ ∧ ‖V‖ ≤ C*‖a‖ ∧
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
          pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))) ∧
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = inverseChartDrift A G P x) := by
  obtain ⟨C₁,hC₁,hprincipal⟩ := exists_chart_coefficient_holder_constant G P
    (hG.of_le (by norm_num)) hP hS hSc hdiam hα hα1
  obtain ⟨C₂,hC₂,hdrift⟩ := exists_inverseChartDrift_holder_constant G P
    hG hP hS hSc hdiam hα hα1
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro A a ha
  have hn (x) (hx : x ∈ S) : ‖A (G x)‖ ≤ ‖a‖ := by
    rw [← ha ⟨G x,hGK hx⟩]; exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le a _
  have hh (x) (hx : x ∈ S) (y) (hy : y ∈ S) :
      ‖A (G x)-A (G y)‖ ≤ ‖a‖*‖G x-G y‖^α := by
    rw [← ha ⟨G x,hGK hx⟩, ← ha ⟨G y,hGK hy⟩]
    simpa only [Subtype.dist_eq, dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le a ⟨G x,hGK hx⟩ ⟨G y,hGK hy⟩
  obtain ⟨hBn,hBh⟩ := hprincipal A ‖a‖ (norm_nonneg a) hn hh
  obtain ⟨hVn,hVh⟩ := hdrift A ‖a‖ (norm_nonneg a) hn hh
  let J : S → E →L[ℝ] E := fun x => fderiv ℝ P (G x)
  have hJ : Continuous J := (hP.continuous_fderiv (by norm_num)).comp
    (hG.continuous.comp continuous_subtype_val)
  have hAg : Continuous (fun x : S => A (G x)) := by
    have hi : Continuous (fun x : S => (⟨G x,hGK x.property⟩ : K)) := by fun_prop
    exact ((OAI.Analysis.Normed.Function.Holder.HolderMap.value a).continuous.comp hi).congr
      (fun x => ha ⟨G x,hGK x.property⟩)
  have hB : Continuous (fun x : S => pullbackEllipticOperator (J x) (A (G x))) :=
    hJ.clm_comp (hAg.clm_comp (ContinuousLinearMap.adjoint.continuous.comp hJ))
  have hH : Continuous (fun x : S => fderiv ℝ (fderiv ℝ G) x) :=
    (((hG.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuous).comp continuous_subtype_val
  have hV : Continuous (fun x : S => inverseChartDrift A G P x) := by
    apply hJ.clm_apply
    apply continuous_finsetSum
    intro i _
    exact (hH.clm_apply (hB.clm_apply continuous_const)).clm_apply continuous_const
  obtain ⟨B,hBval,hBnorm⟩ := exists_holder_on_of_bounds hα (mul_nonneg hC₁.le (norm_nonneg a))
    _ hB (fun x => hBn x x.property) (by
      intro x y
      simpa only [Subtype.dist_eq, dist_eq_norm] using hBh x x.property y y.property)
  obtain ⟨V,hVval,hVnorm⟩ := exists_holder_on_of_bounds hα (mul_nonneg hC₂.le (norm_nonneg a))
    _ hV (fun x => hVn x x.property) (by
      intro x y
      simpa only [Subtype.dist_eq, dist_eq_norm] using hVh x x.property y y.property)
  exact ⟨B,V,hBnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg a)),
    hVnorm.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg a)),hBval,hVval⟩

end OAI.Analysis.PDE.Elliptic
