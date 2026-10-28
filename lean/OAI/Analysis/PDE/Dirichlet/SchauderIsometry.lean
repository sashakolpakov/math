import OAI.Analysis.Normed.Function.Holder.C2HolderIsometry
import OAI.Analysis.Normed.Function.Holder.C2HolderConstruct

open Set
open scoped ContDiff BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

theorem fderiv_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : Differentiable ℝ u) (x v : E) :
    fderiv ℝ (u ∘ e) x v = fderiv ℝ u (e x) (e v) := by
  have hd := ((hu (e x)).hasFDerivAt.comp x
    e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hd

theorem norm_fderiv_isometry_comp_le (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : Differentiable ℝ u) (x : E) :
    ‖fderiv ℝ (u ∘ e) x‖ ≤ ‖fderiv ℝ u (e x)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [fderiv_isometry_comp e u hu]
  simpa only [e.norm_map] using (fderiv ℝ u (e x)).le_opNorm (e v)

theorem norm_second_isometry_comp_le (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 2 u) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x‖ ≤ ‖fderiv ℝ (fderiv ℝ u) (e x)‖ := by
  apply OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback e
  intro v w
  exact second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap x v w

theorem norm_second_sub_isometry_comp_le (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 2 u) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x - fderiv ℝ (fderiv ℝ (u ∘ e)) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ u) (e x) - fderiv ℝ (fderiv ℝ u) (e y)‖ := by
  apply OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback e
  intro v w
  simp only [sub_apply]
  exact congrArg₂ (· - ·)
    (second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap x v w)
    (second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap y v w)

theorem bilinear_norm_eq_isometric_pullback (e : E ≃ₗᵢ[ℝ] F)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ)
    (h : ∀ v w, A v w = B (e v) (e w)) : ‖A‖ = ‖B‖ := by
  apply le_antisymm (OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback e A B h)
  apply OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback e.symm B A
  intro v w
  simpa only [LinearIsometryEquiv.apply_symm_apply] using (h (e.symm v) (e.symm w)).symm

theorem norm_fderiv_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : Differentiable ℝ u) (x : E) :
    ‖fderiv ℝ (u ∘ e) x‖ = ‖fderiv ℝ u (e x)‖ := by
  apply le_antisymm (norm_fderiv_isometry_comp_le e u hu x)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have h := (fderiv ℝ (u ∘ e) x).le_opNorm (e.symm v)
  simpa only [fderiv_isometry_comp e u hu, LinearIsometryEquiv.apply_symm_apply,
    e.symm.norm_map] using h

theorem norm_second_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 2 u) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x‖ = ‖fderiv ℝ (fderiv ℝ u) (e x)‖ := by
  apply bilinear_norm_eq_isometric_pullback e
  intro v w
  exact second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap x v w

theorem norm_second_sub_isometry_comp (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ)
    (hu : ContDiff ℝ 2 u) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x - fderiv ℝ (fderiv ℝ (u ∘ e)) y‖ =
      ‖fderiv ℝ (fderiv ℝ u) (e x) - fderiv ℝ (fderiv ℝ u) (e y)‖ := by
  apply bilinear_norm_eq_isometric_pullback e
  intro v w
  simp only [sub_apply]
  exact congrArg₂ (· - ·)
    (second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap x v w)
    (second_fderiv_comp_between u hu e.toContinuousLinearEquiv.toContinuousLinearMap y v w)

/-- The reverse norm comparison requires only the exact stored jets, not an
extension operator or a boundary regularity premise. -/
theorem C2Holder_norm_le_isometry_pullback
    {Ω K : Set F} (hΩK : Ω ⊆ K) {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) (hu : ContDiff ℝ 2 u)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (V : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) (preimage_mono hΩK : e ⁻¹' Ω ⊆ e ⁻¹' K) α)
    (h0 : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x)
    (h1 : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x)
    (h2 : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x)
    (hv0 : ∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.C2Holder.value V x = u (e x))
    (hv1 : ∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative V x = fderiv ℝ (u ∘ e) x)
    (hv2 : ∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative V x = fderiv ℝ (fderiv ℝ (u ∘ e)) x) :
    ‖U‖ ≤ ‖V‖ := by
  let lift (x : K) : e ⁻¹' K := ⟨e.symm x, by simpa only [mem_preimage,
    LinearIsometryEquiv.apply_symm_apply] using x.property⟩
  have he (x : K) : e (lift x) = (x : F) := e.apply_symm_apply x
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα (norm_nonneg V)
  · intro x
    rw [h0, ← he x, ← hv0]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value V).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le V)
  · intro x
    rw [h1, ← he x, ← norm_fderiv_isometry_comp e u (hu.differentiable (by norm_num)), ← hv1]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative V).norm_coe_le_norm _).trans
      (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le V)
  · intro x
    rw [h2, ← he x, ← norm_second_isometry_comp e u hu, ← hv2]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le V.val.2.2 _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · intro x y
    rw [h2, h2, ← he x, ← he y, ← norm_second_sub_isometry_comp e u hu, ← hv2, ← hv2]
    have h := OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder V (lift x) (lift y)
    have hd : dist (lift x) (lift y) = dist x y := by
      exact e.symm.isometry.dist_eq x y
    simpa only [hd, Subtype.dist_eq, e.isometry.dist_eq] using h

/-- The scalar supremum norm is also unchanged, independently of the higher
jets. This keeps the lower-order term in Schauder estimates unchanged. -/
theorem norm_bounded_isometry_pullback (e : E ≃ₗᵢ[ℝ] F) {K : Set F}
    (f : K →ᵇ ℝ) (g : (e ⁻¹' K) →ᵇ ℝ)
    (h : ∀ x : e ⁻¹' K, g x = f ⟨e x, x.property⟩) : ‖g‖ = ‖f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro x
    rw [h]
    exact f.norm_coe_le_norm _
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
    intro x
    let y : e ⁻¹' K := ⟨e.symm x, by simpa only [mem_preimage,
      LinearIsometryEquiv.apply_symm_apply] using x.property⟩
    have heq : g y = f x := by
      rw [h]
      congr 1
      exact Subtype.ext (e.apply_symm_apply x)
    rw [← heq]
    exact g.norm_coe_le_norm y

/-- A genuine C³ representative and all three stored jets transport to the
preimage domain under an isometry, without any loss in the C²,α norm. -/
theorem exists_C2Holder_isometry_pullback
    {Ω K : Set F} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) {α : ℝ} (hα : 0 ≤ α)
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) (hu : ContDiff ℝ 3 u)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (h0 : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x)
    (h1 : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x)
    (h2 : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) :
    ∃ V : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) (preimage_mono hΩK : e ⁻¹' Ω ⊆ e ⁻¹' K) α,
      ContDiff ℝ 3 (u ∘ e) ∧ ‖V‖ = ‖U‖ ∧
      (∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.C2Holder.value V x = u (e x)) ∧
      (∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative V x = fderiv ℝ (u ∘ e) x) ∧
      (∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative V x = fderiv ℝ (fderiv ℝ (u ∘ e)) x) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have huv : ContDiff ℝ 3 (u ∘ e) := hu.comp e.contDiff
  have hval (x : E) (hx : x ∈ e ⁻¹' K) : ‖u (e x)‖ ≤ ‖U‖ := by
    rw [← h0 ⟨e x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le U)
  have hfirst (x : E) (hx : x ∈ e ⁻¹' K) : ‖fderiv ℝ (u ∘ e) x‖ ≤ ‖U‖ := by
    apply (norm_fderiv_isometry_comp_le e u (hu2.differentiable (by norm_num)) x).trans
    rw [← h1 ⟨e x, hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U).norm_coe_le_norm _).trans
      (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le U)
  have hsecond (x : E) (hx : x ∈ e ⁻¹' K) : ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x‖ ≤ ‖U‖ := by
    apply (norm_second_isometry_comp_le e u hu2 x).trans
    rw [← h2 ⟨e x, hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le U.val.2.2 _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hholder (x : E) (hx : x ∈ e ⁻¹' K) (y : E) (hy : y ∈ e ⁻¹' K) :
      ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x - fderiv ℝ (fderiv ℝ (u ∘ e)) y‖ ≤
        ‖U‖ * dist x y ^ α := by
    apply (norm_second_sub_isometry_comp_le e u hu2 x y).trans
    rw [← h2 ⟨e x, hx⟩, ← h2 ⟨e y, hy⟩]
    simpa only [Subtype.dist_eq, e.isometry.dist_eq] using
      OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder U ⟨e x, hx⟩ ⟨e y, hy⟩
  let V := OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff (hΩ.preimage e.continuous) (preimage_mono hΩK)
    hα (u ∘ e) (huv.of_le (by norm_num)) hval hfirst hsecond hholder
  refine ⟨V, huv, ?_, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  apply le_antisymm ?_ (C2Holder_norm_le_isometry_pullback hΩK hα e u hu2 U V
    h0 h1 h2 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl))
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα (norm_nonneg U)
  · intro x
    exact hval x x.property
  · intro x
    exact hfirst x x.property
  · intro x
    exact hsecond x x.property
  · intro x y
    exact hholder x x.property y y.property

end OAI.Analysis.PDE.Dirichlet
