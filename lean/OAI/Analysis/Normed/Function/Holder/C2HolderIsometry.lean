import OAI.Analysis.Normed.Function.Holder.C2HolderNorm
import OAI.Analysis.Normed.Function.Holder.C2HolderExt
import OAI.Analysis.PDE.Dirichlet.CoordinateTransport

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

abbrev FullSpaceC2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :=
  C2Holder (F := ℝ) (show (univ : Set E) ⊆ univ from Subset.rfl) α

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

local instance isometryFirstENormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance isometryFirstENormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance isometrySecondENormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance isometrySecondENormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance isometryFirstFNormedGroup : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance isometryFirstFNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance isometrySecondFNormedGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance isometrySecondFNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

def fullValue (u : FullSpaceC2 E α) (x : E) : ℝ := OAI.Analysis.Normed.Function.Holder.C2Holder.value u ⟨x, mem_univ x⟩

theorem fullValue_eq_extension (u : FullSpaceC2 E α) :
    fullValue u = boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u) := by
  funext x
  exact (boundedZeroExtension_apply _ (mem_univ x)).symm

theorem contDiff_fullValue (u : FullSpaceC2 E α) : ContDiff ℝ 2 (fullValue u) := by
  rw [fullValue_eq_extension]
  exact contDiffOn_univ.mp (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value isOpen_univ u)

theorem fullValue_first (u : FullSpaceC2 E α) (x : E) :
    fderiv ℝ (fullValue u) x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative u ⟨x, mem_univ x⟩ := by
  rw [fullValue_eq_extension]
  exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives isOpen_univ u (mem_univ x)).1

theorem fullValue_second (u : FullSpaceC2 E α) (x : E) :
    fderiv ℝ (fderiv ℝ (fullValue u)) x = OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u ⟨x, mem_univ x⟩ := by
  rw [fullValue_eq_extension]
  exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives isOpen_univ u (mem_univ x)).2

theorem fullValue_norm_le (u : FullSpaceC2 E α) (x : E) : ‖fullValue u x‖ ≤ ‖u‖ :=
  ((OAI.Analysis.Normed.Function.Holder.C2Holder.value u).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le u)

theorem fullValue_first_norm_le (u : FullSpaceC2 E α) (x : E) :
    ‖fderiv ℝ (fullValue u) x‖ ≤ ‖u‖ := by
  rw [fullValue_first]
  exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative u).norm_coe_le_norm _).trans
    (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le u)

theorem fullValue_second_norm_le (u : FullSpaceC2 E α) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fullValue u)) x‖ ≤ ‖u‖ := by
  rw [fullValue_second]
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le u.val.2.2 _).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem fullValue_second_holder (u : FullSpaceC2 E α) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (fullValue u)) x - fderiv ℝ (fderiv ℝ (fullValue u)) y‖ ≤
      ‖u‖ * (dist x y) ^ α := by
  rw [fullValue_second, fullValue_second]
  exact OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder u ⟨x, mem_univ x⟩ ⟨y, mem_univ y⟩

theorem bilinear_norm_le_isometric_pullback (e : E ≃ₗᵢ[ℝ] F)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ)
    (h : ∀ v w, A v w = B (e v) (e w)) : ‖A‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound A (norm_nonneg B)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [h]
  calc
    _ ≤ ‖B (e v)‖ * ‖e w‖ := (B (e v)).le_opNorm _
    _ ≤ (‖B‖ * ‖e v‖) * ‖e w‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [e.norm_map, e.norm_map]

/-- Isometric coordinate changes preserve the full C²,α norm. -/
theorem exists_fullSpace_pullback (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F)
    (u : FullSpaceC2 F α) :
    ∃ v : FullSpaceC2 E α, fullValue v = fullValue u ∘ e ∧ ‖v‖ ≤ ‖u‖ := by
  let L := e.toContinuousLinearEquiv.toContinuousLinearMap
  let f : E → ℝ := fullValue u ∘ e
  have hf : ContDiff ℝ 2 f := (contDiff_fullValue u).comp e.contDiff
  have hfirst (x : E) : ‖fderiv ℝ f x‖ ≤ ‖u‖ := by
    have hd : fderiv ℝ f x = (fderiv ℝ (fullValue u) (e x)).comp L :=
      (((contDiff_fullValue u).differentiable (by norm_num) (e x)).hasFDerivAt.comp
        x L.hasFDerivAt).fderiv
    rw [hd]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    exact ((fderiv ℝ (fullValue u) (e x)).le_opNorm (e v)).trans
      (by rw [e.norm_map]; exact mul_le_mul_of_nonneg_right (fullValue_first_norm_le u (e x)) (norm_nonneg _))
  have hsecond (x : E) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ‖u‖ := by
    apply (bilinear_norm_le_isometric_pullback e _
      (fderiv ℝ (fderiv ℝ (fullValue u)) (e x)) ?_).trans (fullValue_second_norm_le u (e x))
    intro v w
    exact OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between (fullValue u) (contDiff_fullValue u) L x v w
  have hholder (x y : E) : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
      ‖u‖ * (dist x y) ^ α := by
    have hb := bilinear_norm_le_isometric_pullback e
      (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)
      (fderiv ℝ (fderiv ℝ (fullValue u)) (e x) - fderiv ℝ (fderiv ℝ (fullValue u)) (e y))
      (by
        intro v w
        simp only [sub_apply]
        exact congrArg₂ (· - ·)
          (OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between (fullValue u) (contDiff_fullValue u) L x v w)
          (OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between (fullValue u) (contDiff_fullValue u) L y v w))
    exact hb.trans (by simpa only [e.isometry.dist_eq] using fullValue_second_holder u (e x) (e y))
  let v : FullSpaceC2 E α := OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff isOpen_univ Subset.rfl hα f hf
    (fun x _ ↦ fullValue_norm_le u (e x)) (fun x _ ↦ hfirst x) (fun x _ ↦ hsecond x)
    (fun x _ y _ ↦ hholder x y)
  refine ⟨v, rfl, ?_⟩
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα (norm_nonneg u)
  · intro x
    exact fullValue_norm_le u (e x)
  · intro x
    exact hfirst x
  · intro x
    exact hsecond x
  · intro x y
    exact hholder x y

end OAI.Analysis.Normed.Function.Holder
