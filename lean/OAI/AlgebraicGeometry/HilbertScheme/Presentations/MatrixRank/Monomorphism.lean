import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.ParameterIntersections
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Monomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Monomorphism.Grassmannian

noncomputable section

/-! The actual glued fixed-rank matrix scheme is a monomorphism over its
parameter scheme. Both the topological injectivity and the surjectivity of
stalk maps are proved from the constructed pivot charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

instance matrixRankStructureMap_surjectiveOnStalks :
    SurjectiveOnStalks (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @SurjectiveOnStalks) (Data.Grassmannian.matrixRankGlueData (ι := ι) M A).openCover).mpr
  intro p
  change MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν at p
  change SurjectiveOnStalks (Data.Grassmannian.matrixRankChartMap M A p ≫ Data.Grassmannian.matrixRankStructureMap M A)
  rw [Data.Grassmannian.matrixRankChartMap_structureMap]
  infer_instance

theorem matrixRankStructureMap_injective :
    Function.Injective (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) := by
  intro x y h
  obtain ⟨p, xp, rfl⟩ := Data.Grassmannian.matrixRankCharts_cover M A x
  obtain ⟨q, yq, rfl⟩ := Data.Grassmannian.matrixRankCharts_cover M A y
  have hp : (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left xp =
      (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A q).left yq := by
    rw [← Data.Grassmannian.matrixRankChartMap_structureMap M A p, ← Data.Grassmannian.matrixRankChartMap_structureMap M A q]
    exact h
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
    (MatrixPivot.ParameterIntersections.Grassmannian.matrixPivot_parameter_isPullback M A p q) xp yq hp
  rw [← hz₁, ← hz₂]
  exact congrArg (fun f : (MatrixPivot.Overlaps.Grassmannian.matrixPivotOverlap M A p q).left ⟶ Data.Grassmannian.matrixRankScheme (ι := ι) M A => f z)
    (Data.Grassmannian.matrixRankChart_intersection_isPullback M A p q).w

instance matrixRankStructureMap_mono : Mono (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) :=
  SurjectiveOnStalks.mono_of_injective (matrixRankStructureMap_injective M A)

instance matrixRankParameterMap_mono : Mono (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A) := by
  have : Mono (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A).left :=
    matrixRankStructureMap_mono M A
  exact Over.mono_of_mono_left _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Monomorphism.Grassmannian
