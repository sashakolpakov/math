import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelForms
import OAI.Analysis.HodgeTheory.Integration

/-! # Rechart Partition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartPartition.CM

noncomputable section

/-! ThetaCycle: the same finite set of chart centers and the same cutoff
functions give a genuine smooth partition after changing model coordinates. -/

open Set OAI.Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing
open scoped _root_.Manifold ContDiff

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def linearRechartPartition (e : E ≃L[ℝ] F) (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition E M) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition F M := by
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  let ρ : SmoothPartitionOfUnity D.centers 𝓘(ℝ, F) M := {
    toFun := fun i => ⟨D.partition i,
      (D.partition i).contMDiff.comp (RealModelCharts.CM.linearRechartDiffeomorph (M := M) e ∞).symm.contMDiff⟩
    locallyFinite' := D.partition.locallyFinite
    nonneg' := D.partition.nonneg
    sum_eq_one' := fun _ hx => D.partition.sum_eq_one hx
    sum_le_one' := D.partition.sum_le_one }
  refine ⟨D.centers, ρ, ?_⟩
  intro i
  change tsupport (D.partition i) ⊆
    ((chartAt E i.val).trans e.toHomeomorph.toOpenPartialHomeomorph).source
  simpa only [mfld_simps] using D.subordinate i

theorem linear_rechart_partition_centers (e : E ≃L[ℝ] F) (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition E M) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    (linearRechartPartition e D).centers = D.centers := rfl

theorem linear_rechart_partition_apply (e : E ≃L[ℝ] F) (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (i : D.centers) (x : M) :
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    (linearRechartPartition e D).partition i x = D.partition i x := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartPartition.CM
