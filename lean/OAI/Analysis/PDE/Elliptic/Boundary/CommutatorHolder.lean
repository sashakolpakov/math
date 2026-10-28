import OAI.Analysis.PDE.Elliptic.Boundary.VectorField
import OAI.Analysis.Normed.Function.Holder.Banach.Operator
import OAI.Analysis.Normed.Function.Holder.Banach.Linear

/-! Uniform Hölder bounds for the lower-order commutator. The coefficient
and solution enter only through their existing C^α first and second jets. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder InnerProductSpace

variable {X E F : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

def holderEvaluate (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] F) α) (v : E) : OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map (ContinuousLinearMap.apply ℝ F v) A

omit [FiniteDimensional ℝ E] in
@[simp] theorem value_holderEvaluate (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] F) α) (v : E) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderEvaluate A v) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value A x v := rfl

omit [FiniteDimensional ℝ E] in
theorem holderEvaluate_norm_le (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] F) α) {v : E} (hv : ‖v‖ ≤ 1) :
    ‖holderEvaluate A v‖ ≤ ‖A‖ := by
  have hb : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    exact (L.le_opNorm v).trans (by nlinarith [norm_nonneg L])
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le _ A).trans (by nlinarith [norm_nonneg A])

section Commutator

local instance commutatorFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance commutatorFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance commutatorSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance commutatorSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance commutatorFieldGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance commutatorFieldSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance commutatorFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance commutatorFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def holderFieldCommutator (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (A J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  ∑ i, let b := stdOrthonormalBasis ℝ E i
    OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate A b)) (holderEvaluate J b) +
    OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (holderEvaluate H b) (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα J (holderEvaluate A b)) +
    OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D (holderEvaluate (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα K (holderEvaluate A b)) b)

theorem value_holderFieldCommutator (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (A J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderFieldCommutator hα D H A J K) x =
      ∑ i, let b := stdOrthonormalBasis ℝ E i
        OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x b) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x b) +
        OAI.Analysis.Normed.Function.Holder.HolderMap.value H x b (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x b)) +
        OAI.Analysis.Normed.Function.Holder.HolderMap.value D x (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x b) b) := by
  change OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM (holderFieldCommutator hα D H A J K) x = _
  simp [holderFieldCommutator, map_sum, OAI.Analysis.Normed.Function.Holder.HolderMap.value_add]

theorem holderFieldCommutator_norm_le (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (A J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α) :
    ‖holderFieldCommutator hα D H A J K‖ ≤
      Module.finrank ℝ E * (8 * ‖H‖ * ‖A‖ * ‖J‖ + 4 * ‖D‖ * ‖A‖ * ‖K‖) := by
  unfold holderFieldCommutator
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
        (8 * ‖H‖ * ‖A‖ * ‖J‖ + 4 * ‖D‖ * ‖A‖ * ‖K‖) := by
      apply Finset.sum_le_sum
      intro i _
      let b := stdOrthonormalBasis ℝ E i
      have hb : ‖b‖ ≤ 1 := (stdOrthonormalBasis ℝ E).norm_eq_one i |>.le
      have h1 : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (holderEvaluate A b))
          (holderEvaluate J b)‖ ≤ 4 * ‖H‖ * ‖A‖ * ‖J‖ := by
        apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
        calc
          _ ≤ 2 * (2 * ‖H‖ * ‖A‖) * ‖J‖ := by
            gcongr
            · exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
                (mul_le_mul_of_nonneg_left (holderEvaluate_norm_le A hb) (by positivity))
            · exact holderEvaluate_norm_le J hb
          _ = _ := by ring
      have h2 : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (holderEvaluate H b)
          (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα J (holderEvaluate A b))‖ ≤ 4 * ‖H‖ * ‖A‖ * ‖J‖ := by
        apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
        calc
          _ ≤ 2 * ‖H‖ * (2 * ‖J‖ * ‖A‖) := by
            gcongr
            · exact holderEvaluate_norm_le H hb
            · exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
                (mul_le_mul_of_nonneg_left (holderEvaluate_norm_le A hb) (by positivity))
          _ = _ := by ring
      have h3 : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D
          (holderEvaluate (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα K (holderEvaluate A b)) b)‖ ≤
          4 * ‖D‖ * ‖A‖ * ‖K‖ := by
        apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
        calc
          _ ≤ 2 * ‖D‖ * (2 * ‖K‖ * ‖A‖) := by
            gcongr
            exact (holderEvaluate_norm_le _ hb).trans
              ((OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
                (mul_le_mul_of_nonneg_left (holderEvaluate_norm_le A hb) (by positivity)))
          _ = _ := by ring
      exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans (by linarith)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Commutator
end OAI.Analysis.PDE.Elliptic
