import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Data

/-! # Parameter Intersections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.ParameterIntersections.Grassmannian

noncomputable section

/-! The glued pivot overlaps are the actual fiber products of chart inclusions into the parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

theorem matrixPivot_parameter_isPullback_over (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsPullback (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q)
      (Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p)
      (Charts.Grassmannian.matrixPivotChartInclusion M A p) (Charts.Grassmannian.matrixPivotChartInclusion M A q) := by
  apply IsPullback.mk'
  · rw [Category.assoc]
    exact (Overlaps.Grassmannian.matrixPivotOverlapSwap_parameter M A p q).symm
  · intro T f g h _
    exact (cancel_mono (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q)).mp h
  · intro T f g h
    have hu : IsUnit ((f ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p).left.appTop (A.submatrix q.2 q.1).det) := by
      rw [h]
      exact (Charts.Grassmannian.matrixPivotChart_condition M A q g).1
    let y := Overlaps.Grassmannian.matrixPivotOverlapLift M A p q f hu
    have hy : y ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q = f := Overlaps.Grassmannian.matrixPivotOverlapLift_inclusion M A p q f hu
    refine ⟨y, hy, ?_⟩
    apply (cancel_mono (Charts.Grassmannian.matrixPivotChartInclusion M A q)).mp
    calc
      (y ≫ (Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p)) ≫
          Charts.Grassmannian.matrixPivotChartInclusion M A q =
          y ≫ (Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A q p) := by
            simp only [Overlaps.Grassmannian.matrixPivotOverlapParameter, Category.assoc]
      _ = y ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A p q := by rw [Overlaps.Grassmannian.matrixPivotOverlapSwap_parameter]
      _ = (y ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q) ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p :=
        (Category.assoc _ _ _).symm
      _ = f ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p := by rw [hy]
      _ = g ≫ Charts.Grassmannian.matrixPivotChartInclusion M A q := h

theorem matrixPivot_parameter_isPullback (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsPullback (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q).left
      (Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p).left
      (Charts.Grassmannian.matrixPivotChartInclusion M A p).left (Charts.Grassmannian.matrixPivotChartInclusion M A q).left :=
  (matrixPivot_parameter_isPullback_over M A p q).map (Over.forget S)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.ParameterIntersections.Grassmannian
