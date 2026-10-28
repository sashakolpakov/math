import OAI.Analysis.Normed.Function.Holder.C2HolderJointClosed

/-! Closed-domain joint evaluation in a fixed physical chart. -/
noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {Z E F X : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U : Set Z} {S : Set X} {r : E → ℝ} {α : ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}

omit [Nontrivial E] in
theorem contDiffOn_joint_value_closed_chart
    (hU : IsOpen U) (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 2 u U)
    (G : X → E) (hG : ContDiffOn ℝ 2 G S) (hGS : MapsTo G S {x | r x ≤ 0}) :
    ContDiffOn ℝ 2 (fun p : Z × X => boundedZeroExtension (C2Holder.value (u p.1)) (G p.2))
      (U ×ˢ S) := by
  have hmap : ContDiffOn ℝ 2 (fun p : Z × X => (p.1,G p.2)) (U ×ˢ S) :=
    contDiffOn_fst.prodMk (hG.comp contDiffOn_snd (fun p hp => hp.2))
  exact (C2Holder.contDiffOn_joint_value_closed hU hr hreg u hu).comp hmap
    (fun p hp => ⟨hp.1,hGS hp.2⟩)

omit [Nontrivial E] in
theorem contDiffOn_joint_value_parameterDirections_closed_chart
    (hU : IsOpen U) (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ ∞ u U) (ws : List Z)
    (G : X → E) (hG : ContDiffOn ℝ 2 G S) (hGS : MapsTo G S {x | r x ≤ 0}) :
    ContDiffOn ℝ 2 (fun p : Z × X =>
      boundedZeroExtension (C2Holder.value (parameterDirections u ws p.1)) (G p.2)) (U ×ˢ S) :=
  C2Holder.contDiffOn_joint_value_closed_chart hU hr hreg (parameterDirections u ws)
    ((contDiffOn_parameterDirections hU u hu ws).of_le (by simp)) G hG hGS

end OAI.Analysis.Normed.Function.Holder.C2Holder
