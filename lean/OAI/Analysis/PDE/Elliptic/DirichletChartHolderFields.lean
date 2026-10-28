import OAI.Analysis.PDE.Elliptic.Boundary.ConvexExtension
import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.DriftHolder

open Set InnerProductSpace
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Norm and difference bounds on a closed convex patch give an actual
global Hölder field agreeing there, with no extra extension hypothesis. -/
theorem exists_convex_holder_extension_of_bounds {K : Set E}
    (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K)
    {α M : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M) (f : K → F) (hf : Continuous f)
    (hn : ∀ x, ‖f x‖ ≤ M)
    (hh : ∀ x y, ‖f x - f y‖ ≤ M * dist x y ^ α) :
    ∃ g : OAI.Analysis.Normed.Function.Holder.HolderMap E F α, (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value g x = f x) ∧ ‖g‖ ≤ M := by
  let v : K →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup f hf M hn
  let U := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh
  obtain ⟨g, hg, hgn⟩ := exists_convex_holder_extension hne hc hconv hα U
  refine ⟨g, hg, hgn.trans ?_⟩
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα v hM hh).trans
  exact max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hf hM hn) le_rfl

variable [FiniteDimensional ℝ E]

theorem continuous_inverseChartDrift
    {A : E → E →L[ℝ] E} (hA : Continuous A)
    {G P : E → E} (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P) :
    Continuous (inverseChartDrift A G P) := by
  let J := fun x => fderiv ℝ P (G x)
  have hJ : Continuous J := (hP.continuous_fderiv (by norm_num)).comp hG.continuous
  have hH : Continuous (fderiv ℝ (fderiv ℝ G)) :=
    ((hG.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  have hB : Continuous (fun x => pullbackEllipticOperator (J x) (A (G x))) := by
    exact hJ.clm_comp ((hA.comp hG.continuous).clm_comp
      (ContinuousLinearMap.adjoint.continuous.comp hJ))
  unfold inverseChartDrift chartDrift
  apply hJ.clm_apply
  apply continuous_finsetSum
  intro i _
  exact (hH.clm_apply (hB.clm_apply continuous_const)).clm_apply continuous_const

/-- Fixed charts yield uniformly bounded global Hölder representatives
for the transformed principal coefficient and the actual first-order
drift. No derivatives or off-patch bounds of A enter the constant. -/
theorem exists_chart_holder_fields
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P)
    {S : Set E} (hne : S.Nonempty) (hS : IsCompact S) (hSc : Convex ℝ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ A : E → E →L[ℝ] E, Continuous A → ∀ N : ℝ, 0 ≤ N →
      (∀ x ∈ S, ‖A (G x)‖ ≤ N) →
      (∀ x ∈ S, ∀ y ∈ S, ‖A (G x)-A (G y)‖ ≤ N * ‖G x-G y‖^α) →
      ∃ (B : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] E) α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α),
        ‖B‖ ≤ C*N ∧ ‖b‖ ≤ C*N ∧
        (∀ x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
          pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))) ∧
        (∀ x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value b x = inverseChartDrift A G P x) := by
  obtain ⟨C₁, hC₁, hprincipal⟩ := exists_chart_coefficient_holder_constant G P
    (hG.of_le (by norm_num)) hP hS hSc hdiam hα hα1
  obtain ⟨C₂, hC₂, hdrift⟩ := exists_inverseChartDrift_holder_constant G P
    hG hP hS hSc hdiam hα hα1
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro A hA N hN hAn hAh
  obtain ⟨hBn, hBh⟩ := hprincipal A N hN hAn hAh
  obtain ⟨hbn, hbh⟩ := hdrift A N hN hAn hAh
  let B₀ := fun x => pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))
  have hJ : Continuous (fun x => fderiv ℝ P (G x)) :=
    (hP.continuous_fderiv (by norm_num)).comp hG.continuous
  have hB₀ : Continuous B₀ := hJ.clm_comp ((hA.comp hG.continuous).clm_comp
    (ContinuousLinearMap.adjoint.continuous.comp hJ))
  obtain ⟨B, hB, hBn'⟩ := exists_convex_holder_extension_of_bounds hne hS.isComplete hSc
    hα (mul_nonneg hC₁.le hN) (fun x : S => B₀ x) (hB₀.comp continuous_subtype_val)
    (fun x => hBn x x.property) (by
      intro x y
      simpa only [Subtype.dist_eq, dist_eq_norm] using hBh x x.property y y.property)
  obtain ⟨b, hb, hbn'⟩ := exists_convex_holder_extension_of_bounds hne hS.isComplete hSc
    hα (mul_nonneg hC₂.le hN) (fun x : S => inverseChartDrift A G P x)
    ((continuous_inverseChartDrift hA hG hP).comp continuous_subtype_val)
    (fun x => hbn x x.property) (by
      intro x y
      simpa only [Subtype.dist_eq, dist_eq_norm] using hbh x x.property y y.property)
  exact ⟨B, b, hBn'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hN),
    hbn'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hN),
    fun x hx => hB ⟨x, hx⟩, fun x hx => hb ⟨x, hx⟩⟩

end OAI.Analysis.PDE.Elliptic
