import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Equations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.AmbientOpen

/-! # Ambient Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.AmbientPullback.Grassmannian

noncomputable section

/-! Pulling the matrix-rank scheme back to an ambient determinant-open gives
exactly the corresponding closed pivot chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

theorem matrixRank_global_pivot_of_unit (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν)
    {T : Over S} (x : T ⟶ M) (hx : Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A x)
    (hu : IsUnit (x.left.appTop (A.submatrix p.2 p.1).det)) :
    MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
      (A.submatrix id p.1) A x.left.appTop.hom := by
  obtain ⟨U, hU⟩ := (Equations.Grassmannian.matrixRankLocalCondition_iff_equations M A x).mp hx
  apply (Equations.Grassmannian.matrixPivotChart_factorization_iff M A p x.left).mpr
  apply Local.MorphismFactorization.lift_of_openCover U x.left (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left
  intro i
  obtain ⟨q, hq⟩ := hU i
  have hpunit : IsUnit ((U.f i ≫ x.left).appTop (A.submatrix p.2 p.1).det) :=
    hu.map (U.f i).appTop.hom
  have hp := MatrixPivot.Condition.Grassmannian.fullMatrixPivotCondition_transition A q.1 p.1 q.2 p.2
    (U.f i ≫ x.left).appTop.hom hq hpunit
  obtain ⟨g, hg, _⟩ := (Equations.Grassmannian.matrixPivotChart_factorization_iff M A p _).mp hp
  exact ⟨g, hg⟩

instance matrixRankChartOverMap_mono (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    Mono (Data.Grassmannian.matrixRankChartOverMap M A p) := by
  have : Mono (Data.Grassmannian.matrixRankChartOverMap M A p).left :=
    inferInstanceAs (Mono (Data.Grassmannian.matrixRankChartMap M A p))
  exact Over.mono_of_mono_left _

theorem matrixPivotAmbientOpen_isPullback_over (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsPullback (Data.Grassmannian.matrixRankChartOverMap M A p) (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen M A p)
      (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A) (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotAmbientOpenInclusion M A p) := by
  apply IsPullback.mk'
  · rw [Data.Grassmannian.matrixRankChartOverMap_parameterMap, MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen_inclusion]
  · intro T f g h _
    exact (cancel_mono (Data.Grassmannian.matrixRankChartOverMap M A p)).mp h
  · intro T f g h
    have hlocal : Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A (f ≫ Data.Grassmannian.matrixRankParameterMap M A) :=
      (Representation.Grassmannian.matrixRankLocalCondition_iff_lift M A _).mpr
        ⟨f, rfl, fun z hz => (cancel_mono (Data.Grassmannian.matrixRankParameterMap M A)).mp hz⟩
    have hunit : IsUnit ((f ≫ Data.Grassmannian.matrixRankParameterMap M A).left.appTop (A.submatrix p.2 p.1).det) := by
      rw [h]
      exact (Relative.UnitOpen.relativeUnitOpenInclusion_isUnit M (A.submatrix p.2 p.1).det).map g.left.appTop.hom
    have hp := matrixRank_global_pivot_of_unit M A p (f ≫ Data.Grassmannian.matrixRankParameterMap M A) hlocal hunit
    let y := MatrixPivot.Charts.Grassmannian.matrixPivotChartLift M A p (f ≫ Data.Grassmannian.matrixRankParameterMap M A) hp
    have hy : y ≫ MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p = f ≫ Data.Grassmannian.matrixRankParameterMap M A :=
      MatrixPivot.Charts.Grassmannian.matrixPivotChartLift_inclusion M A p _ hp
    refine ⟨y, ?_, ?_⟩
    · apply (cancel_mono (Data.Grassmannian.matrixRankParameterMap M A)).mp
      rw [Category.assoc, Data.Grassmannian.matrixRankChartOverMap_parameterMap]
      exact hy
    · apply (cancel_mono (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotAmbientOpenInclusion M A p)).mp
      rw [Category.assoc, MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen_inclusion]
      exact hy.trans h

theorem matrixPivotAmbientOpen_isPullback (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsPullback (Data.Grassmannian.matrixRankChartMap M A p) (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen M A p).left
      (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotAmbientOpenInclusion M A p).left :=
  (matrixPivotAmbientOpen_isPullback_over M A p).map (Over.forget S)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.AmbientPullback.Grassmannian
