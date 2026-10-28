import OAI.Analysis.PDE.Elliptic.Boundary.CommutatorHolder
import OAI.Analysis.PDE.Elliptic.Boundary.FieldRemainder
import OAI.Analysis.PDE.Elliptic.Boundary.VectorFieldLocal

/-! The prescribed boundary extension contributes an explicit controlled
Hölder source when subtracted from a differentiated chart equation. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {α : ℝ}

local instance boundaryTraceHolderFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance boundaryTraceHolderFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance boundaryTraceHolderSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryTraceHolderSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryTraceHolderEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance boundaryTraceHolderEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

def holderEllipticTrace (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  ∑ i, holderEvaluate (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H
    (holderEvaluate A (stdOrthonormalBasis ℝ E i))) (stdOrthonormalBasis ℝ E i)

theorem value_holderEllipticTrace (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderEllipticTrace hα A H) x =
      ∑ i, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x (stdOrthonormalBasis ℝ E i))
        (stdOrthonormalBasis ℝ E i) := by
  change OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM (holderEllipticTrace hα A H) x = _
  simp [holderEllipticTrace, map_sum]

theorem holderEllipticTrace_norm_le (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) :
    ‖holderEllipticTrace hα A H‖ ≤ (Module.finrank ℝ E : ℝ) * (2 * ‖H‖ * ‖A‖) := by
  unfold holderEllipticTrace
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), 2 * ‖H‖ * ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hi : ‖stdOrthonormalBasis ℝ E i‖ ≤ 1 := (stdOrthonormalBasis ℝ E).norm_eq_one i |>.le
      exact (holderEvaluate_norm_le _ hi).trans ((OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
        (mul_le_mul_of_nonneg_left (holderEvaluate_norm_le A hi) (by positivity)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem ellipticTrace_sub_at (A : E → E →L[ℝ] E) {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    ellipticTrace A (fun y => u y-v y) x = ellipticTrace A u x-ellipticTrace A v x := by
  obtain ⟨u', hu', heu⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hu
  obtain ⟨v', hv', hev⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hv
  have hsub : (fun y => u' y-v' y) =ᶠ[nhds x] (fun y => u y-v y) := heu.sub hev
  have hs := ellipticTrace_sub A hu' hv' x
  rw [ellipticTrace_congr_germ A hsub, ellipticTrace_congr_germ A heu,
    ellipticTrace_congr_germ A hev] at hs
  exact hs

theorem exists_subtracted_holder_source {S : Set E} (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (a : E → E →L[ℝ] E) (u v : E → ℝ)
    (hA : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a x)
    (hH : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ v) x)
    (hu : ∀ x : S, ContDiffAt ℝ 2 u x) (hv : ∀ x : S, ContDiffAt ℝ 2 v x)
    (heq : ∀ x : S, ellipticTrace a u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) :
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α,
      (∀ x : S, ellipticTrace a (fun y => u y-v y) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x) ∧
      ‖Q‖ ≤ ‖R‖ + (Module.finrank ℝ E : ℝ) * (2 * ‖H‖ * ‖A‖) := by
  refine ⟨R-holderEllipticTrace hα A H, ?_, ?_⟩
  · intro x
    rw [ellipticTrace_sub_at a (hu x) (hv x), heq x, ellipticTrace_eq_hessian_sum a (hv x)]
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value R x - _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x - OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderEllipticTrace hα A H) x
    rw [value_holderEllipticTrace]
    simp only [hA, hH]
  · exact (norm_sub_le _ _).trans (add_le_add le_rfl (holderEllipticTrace_norm_le hα A H))

end OAI.Analysis.PDE.Elliptic
