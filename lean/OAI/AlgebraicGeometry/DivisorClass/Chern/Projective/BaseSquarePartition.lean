import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.SquarePartition

/-! # Base Square Partition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseSquarePartition

noncomputable section

/-! The fixed original base-chart partition normalized so that its squares sum to one. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def projectiveBaseSquarePartition (i : BasePartition.projectiveBaseFiniteCover V) : V.analyticSpace → ℝ :=
  SquarePartition.squarePartitionNormalized (fun j => BasePartition.projectiveBaseSmoothPartition V j) i

theorem projectiveBaseSquarePartition_sum_sq (x : V.analyticSpace) :
    ∑ i, projectiveBaseSquarePartition V i x ^ 2 = 1 :=
  SquarePartition.squarePartitionNormalized_sum_sq (fun j => BasePartition.projectiveBaseSmoothPartition V j)
    (BasePartition.projectiveBaseSmoothPartition_sum V) x

theorem projectiveBaseSquarePartition_smooth (i : BasePartition.projectiveBaseFiniteCover V) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ (projectiveBaseSquarePartition V i) :=
  SquarePartition.squarePartitionNormalized_smooth (fun j => BasePartition.projectiveBaseSmoothPartition V j)
    (BasePartition.projectiveBaseSmoothPartition_smooth V) (BasePartition.projectiveBaseSmoothPartition_sum V) i

theorem projectiveBaseSquarePartition_support (i : BasePartition.projectiveBaseFiniteCover V) :
    tsupport (projectiveBaseSquarePartition V i) ⊆ (chartAt V.analyticModel i.val).source :=
  (SquarePartition.squarePartitionNormalized_tsupport (fun j => BasePartition.projectiveBaseSmoothPartition V j) i).trans
    (BasePartition.projectiveBaseSmoothPartition_support V i)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BaseSquarePartition
