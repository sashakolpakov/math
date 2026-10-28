import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.FlatRankLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.AmbientOpen

/-! # Finite Type -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.FiniteType.Grassmannian

noncomputable section

/-! The representing matrix-rank morphism is locally of finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

instance matrixRankStructureMap_locallyOfFiniteType :
    LocallyOfFiniteType (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyOfFiniteType) (Data.Grassmannian.matrixRankGlueData (ι := ι) M A).openCover).mpr
  intro p
  change MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν at p
  change LocallyOfFiniteType (Data.Grassmannian.matrixRankChartMap M A p ≫ Data.Grassmannian.matrixRankStructureMap M A)
  rw [Data.Grassmannian.matrixRankChartMap_structureMap]
  infer_instance

instance matrixRankParameterMap_locallyOfFiniteType :
    LocallyOfFiniteType (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A).left :=
  matrixRankStructureMap_locallyOfFiniteType M A

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.FiniteType.Grassmannian
