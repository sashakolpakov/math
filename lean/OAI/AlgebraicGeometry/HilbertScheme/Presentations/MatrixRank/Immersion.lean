import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.AmbientPullback
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Immersion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Immersion.Grassmannian

noncomputable section

/-! The flat fixed-rank cokernel locus is a locally closed immersion: on each
ambient pivot-determinant open it is the corresponding closed pivot chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

theorem matrixRank_restrict_minor_closed (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsClosedImmersion (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A ∣_ M.left.basicOpen (A.submatrix p.2 p.1).det) := by
  let U := M.left.basicOpen (A.submatrix p.2 p.1).det
  let f := Data.Grassmannian.matrixRankStructureMap (ι := ι) M A
  have hp : IsPullback (Data.Grassmannian.matrixRankChartMap M A p) (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen M A p).left f U.ι :=
    AmbientPullback.Grassmannian.matrixPivotAmbientOpen_isPullback M A p
  have hq := (isPullback_morphismRestrict f U).flip
  let e := hp.isoIsPullback _ _ hq
  have he : e.inv ≫ (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen M A p).left = f ∣_ U :=
    hp.isoIsPullback_inv_snd _ _ hq
  have : IsIso e.inv := e.isIso_inv
  have hc : IsClosedImmersion (e.inv ≫ (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChartToAmbientOpen M A p).left) := inferInstance
  exact he ▸ hc

theorem matrixRank_range_subset_minor_opens :
    Set.range (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) ⊆
      (⨆ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν, M.left.basicOpen (A.submatrix p.2 p.1).det : M.left.Opens) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, y, rfl⟩ := Data.Grassmannian.matrixRankCharts_cover M A x
  rw [← Scheme.Hom.comp_apply, Data.Grassmannian.matrixRankChartMap_structureMap]
  apply (le_iSup (fun q : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν => M.left.basicOpen (A.submatrix q.2 q.1).det) p)
  exact (OpenUnitLocus.isUnit_appTop_iff_range_subset (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left _).mp
    (MatrixPivot.AmbientOpen.Grassmannian.matrixPivotChart_unit M A p) ⟨y, rfl⟩

instance matrixRankStructureMap_isImmersion : IsImmersion (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) := by
  have : MorphismProperty.RespectsRight @IsImmersion.{u} @IsOpenImmersion.{u} := {
    postcomp := by
      intro X Y Z g hg f hf
      let := hg
      let := hf
      infer_instance }
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion)
    (fun p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν => M.left.basicOpen (A.submatrix p.2 p.1).det)
    (matrixRank_range_subset_minor_opens M A)
  intro p
  let := matrixRank_restrict_minor_closed M A p
  infer_instance

instance matrixRankParameterMap_isImmersion : IsImmersion (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A).left :=
  matrixRankStructureMap_isImmersion M A

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Immersion.Grassmannian
