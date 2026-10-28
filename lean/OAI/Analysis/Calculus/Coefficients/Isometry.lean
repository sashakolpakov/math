import OAI.Analysis.Calculus.Coefficients.Potential
import OAI.Analysis.Normed.Function.Holder.C2HolderIsometry

open Set Filter _root_.MeasureTheory Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance firstENormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance firstENormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance secondENormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance firstFNormedGroup : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance firstFNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance secondFNormedGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

theorem first_fderiv_isometric_norm_le
    (L : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (hf : Differentiable ℝ f) (x : E) :
    ‖fderiv ℝ (f ∘ L) x‖ ≤ ‖fderiv ℝ f (L x)‖ := by
  have he : fderiv ℝ (f ∘ L) x = (fderiv ℝ f (L x)).comp L.toContinuousLinearEquiv.toContinuousLinearMap :=
    ((hf (L x)).hasFDerivAt.comp x L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [he]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,L.norm_map] using (fderiv ℝ f (L x)).le_opNorm (L v)

theorem first_fderiv_isometric_sub_norm_le
    (L : E ≃ₗᵢ[ℝ] F) (f g : F → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x y : E) :
    ‖fderiv ℝ (f ∘ L) x-fderiv ℝ (g ∘ L) y‖ ≤
      ‖fderiv ℝ f (L x)-fderiv ℝ g (L y)‖ := by
  have hf' := ((hf (L x)).hasFDerivAt.comp x L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  have hg' := ((hg (L y)).hasFDerivAt.comp y L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ L) x = _ at hf'
  change fderiv ℝ (g ∘ L) y = _ at hg'
  rw [hf',hg']
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖fderiv ℝ f (L x) (L v)-fderiv ℝ g (L y) (L v)‖ ≤ _
  simpa only [sub_apply,L.norm_map] using
    (fderiv ℝ f (L x)-fderiv ℝ g (L y)).le_opNorm (L v)

theorem second_fderiv_isometric_norm_le
    (L : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ L)) x‖ ≤ ‖fderiv ℝ (fderiv ℝ f) (L x)‖ := by
  apply OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback L
  intro v w
  exact OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between f hf L.toContinuousLinearEquiv.toContinuousLinearMap x v w

theorem second_fderiv_isometric_sub_norm_le
    (L : E ≃ₗᵢ[ℝ] F) (f g : F → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ L)) x-fderiv ℝ (fderiv ℝ (g ∘ L)) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (L x)-fderiv ℝ (fderiv ℝ g) (L y)‖ := by
  apply OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback L
  intro v w
  simp only [sub_apply]
  exact congrArg₂ (· - ·)
    (OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between f hf L.toContinuousLinearEquiv.toContinuousLinearMap x v w)
    (OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between g hg L.toContinuousLinearEquiv.toContinuousLinearMap y v w)

theorem first_jet_uniform_isometric_pullback
    (L : E ≃ₗᵢ[ℝ] F) (u : ℕ → F → ℝ) (f : F → ℝ)
    (hu : ∀ j, Differentiable ℝ (u j)) (hf : Differentiable ℝ f) {K : Set E}
    (h : TendstoUniformlyOn (fun j ↦ fderiv ℝ (u j)) (fderiv ℝ f) atTop (L '' K)) :
    TendstoUniformlyOn (fun j ↦ fderiv ℝ (u j ∘ L)) (fderiv ℝ (f ∘ L)) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff (α := F →L[ℝ] ℝ)).mp h ε hε] with j hj
  intro x hx
  have hn := first_fderiv_isometric_sub_norm_le L f (u j) hf (hu j) x x
  simpa only [dist_eq_norm] using
    hn.trans_lt (by simpa only [dist_eq_norm] using hj (L x) ⟨x,hx,rfl⟩)

theorem second_jet_uniform_isometric_pullback
    (L : E ≃ₗᵢ[ℝ] F) (u : ℕ → F → ℝ) (f : F → ℝ)
    (hu : ∀ j, ContDiff ℝ 2 (u j)) (hf : ContDiff ℝ 2 f) {K : Set E}
    (h : TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (u j)))
      (fderiv ℝ (fderiv ℝ f)) atTop (L '' K)) :
    TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (u j ∘ L)))
      (fderiv ℝ (fderiv ℝ (f ∘ L))) atTop K := by
  refine (Metric.tendstoUniformlyOn_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).mpr ?_
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff (α := F →L[ℝ] F →L[ℝ] ℝ)).mp h ε hε] with j hj
  intro x hx
  have hn := second_fderiv_isometric_sub_norm_le L f (u j) hf (hu j) x x
  have hjx := hj (L x) ⟨x,hx,rfl⟩
  rw [dist_eq_norm] at hjx ⊢
  exact hn.trans_lt hjx

end OAI.Analysis.Calculus.Coefficients
