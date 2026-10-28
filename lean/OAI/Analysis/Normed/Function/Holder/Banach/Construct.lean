import OAI.Analysis.Normed.Function.Holder.Banach
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

def differenceQuotient (α : ℝ) (f : X → F) (q : DistinctPairs X) : F :=
  ((dist q.val.1 q.val.2) ^ α)⁻¹ • (f q.val.1 - f q.val.2)

theorem continuous_differenceQuotient {α : ℝ} (hα : 0 ≤ α) {f : X → F}
    (hf : Continuous f) : Continuous (differenceQuotient α f) := by
  have hd : Continuous (fun q : DistinctPairs X ↦ dist q.val.1 q.val.2) :=
    continuous_subtype_val.fst.dist continuous_subtype_val.snd
  have hw : Continuous (fun q : DistinctPairs X ↦ ((dist q.val.1 q.val.2) ^ α)⁻¹) :=
    ((Real.continuous_rpow_const hα).comp hd).inv₀
      (fun q ↦ (Real.rpow_pos_of_pos (dist_pos.mpr q.property) α).ne')
  exact hw.smul ((hf.comp continuous_subtype_val.fst).sub
    (hf.comp continuous_subtype_val.snd))

theorem norm_differenceQuotient_le {α C : ℝ} {f : X → F}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * (dist x y) ^ α) (q : DistinctPairs X) :
    ‖differenceQuotient α f q‖ ≤ C := by
  have hw : 0 < (dist q.val.1 q.val.2) ^ α :=
    Real.rpow_pos_of_pos (dist_pos.mpr q.property) α
  unfold differenceQuotient
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
  calc
    _ ≤ ((dist q.val.1 q.val.2) ^ α)⁻¹ * (C * (dist q.val.1 q.val.2) ^ α) :=
      mul_le_mul_of_nonneg_left (hf _ _) (inv_nonneg.mpr hw.le)
    _ = C := by field_simp

namespace HolderMap

/-- Insert an actual bounded continuous Hölder function into the complete graph space. -/
def ofBounded {α : ℝ} (hα : 0 ≤ α) (f : X →ᵇ F) {C : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * (dist x y) ^ α) : HolderMap X F α := by
  let q : DistinctPairs X →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (differenceQuotient α f) (continuous_differenceQuotient hα f.continuous) C
    (norm_differenceQuotient_le hf)
  refine ⟨(f, q), ?_⟩
  intro p
  change (dist p.val.1 p.val.2) ^ α •
      (((dist p.val.1 p.val.2) ^ α)⁻¹ • (f p.val.1 - f p.val.2)) = _
  rw [smul_smul, mul_inv_cancel₀ (Real.rpow_pos_of_pos (dist_pos.mpr p.property) α).ne', one_smul]

theorem value_ofBounded {α : ℝ} (hα : 0 ≤ α) (f : X →ᵇ F) {C : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * (dist x y) ^ α) :
    HolderMap.value (HolderMap.ofBounded hα f hf) = f := rfl

theorem norm_ofBounded_le {α : ℝ} (hα : 0 ≤ α) (f : X →ᵇ F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * (dist x y) ^ α) :
    ‖HolderMap.ofBounded hα f hf‖ ≤ max ‖f‖ C := by
  change max ‖f‖ ‖BoundedContinuousFunction.ofNormedAddCommGroup
    (differenceQuotient α f) (continuous_differenceQuotient hα f.continuous) C
    (norm_differenceQuotient_le hf)‖ ≤ max ‖f‖ C
  apply max_le_max le_rfl
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC
    (norm_differenceQuotient_le hf)

theorem value_injective {α : ℝ} : Function.Injective (HolderMap.value (X := X) (F := F) (α := α)) := by
  intro f g hfg
  apply Subtype.ext
  apply Prod.ext
  · exact hfg
  · apply BoundedContinuousFunction.ext
    intro q
    have heval (x) : f.val.1 x = g.val.1 x := congrArg (fun h : X →ᵇ F ↦ h x) hfg
    have h : (dist q.val.1 q.val.2) ^ α • f.val.2 q =
        (dist q.val.1 q.val.2) ^ α • g.val.2 q := by
      rw [f.property q, g.property q, heval, heval]
    have hw : (dist q.val.1 q.val.2) ^ α ≠ 0 :=
      (Real.rpow_pos_of_pos (dist_pos.mpr q.property) α).ne'
    have hi := congrArg (fun z : F ↦ ((dist q.val.1 q.val.2) ^ α)⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hw, one_smul] using hi

end HolderMap
end OAI.Analysis.Normed.Function.Holder
