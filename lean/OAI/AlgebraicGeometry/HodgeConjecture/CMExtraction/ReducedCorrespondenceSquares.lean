import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondence

/-! # Reduced Correspondence Squares -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient

noncomputable section

/-! The source and target squares commute as actual scheme morphisms.
These equalities identify the pulled-back universal PEL families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {B B' : Scheme.{u}} (p : B' ⟶ B) (M : Over B)
  {X : Over B'}
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M)) (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M)

abbrev originalSpaceMap : X.left ⟶ M.left :=
  (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e).left ≫ pullback.fst M.hom p

theorem originalSpaceMap_eq :
    originalSpaceMap p M e = e.hom.left ≫
      pullback.fst (PELModuli.IntegralModel.Reduction.reduction M).hom p ≫ (PELModuli.IntegralModel.Reduction.reductionι M).left := by
  simp only [originalSpaceMap, ReducedModelComparison.IsogenyQuotient.reducedModelMap, Over.comp_left,
    Over.pullback_map_left, Category.assoc, pullback.lift_fst]

variable [IsReduced X.left] [IsLocallyNoetherian X.left]

abbrev originalCoverMap : (ReducedCorrespondence.IsogenyQuotient.modelCover p M e C).left ⟶ C.cover.left :=
  (pullback.fst (C.baseChange p).source (ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e)).left ≫
    pullback.fst C.cover.hom p

theorem baseChange_map_projection {V W : Over B} (f : V ⟶ W) {Z : Over B'}
    (z : Z ⟶ (Over.pullback p).obj V) :
    (z.left ≫ pullback.fst V.hom p) ≫ f.left =
      (z ≫ (Over.pullback p).map f).left ≫ pullback.fst W.hom p := by
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]

theorem originalCoverMap_source :
    originalCoverMap p M e C ≫ C.source.left =
      (ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).source.left ≫ originalSpaceMap p M e := by
  rw [originalCoverMap, baseChange_map_projection]
  have hc := congrArg (fun f => f.left ≫ pullback.fst M.hom p)
    (pullback.condition (f := (C.baseChange p).source) (g := ReducedModelComparison.IsogenyQuotient.reducedModelMap p M e))
  exact hc.trans (Category.assoc _ _ _)

theorem originalCoverMap_target :
    originalCoverMap p M e C ≫ C.target.left =
      (ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M e C).target.left ≫ originalSpaceMap p M e := by
  rw [originalCoverMap, baseChange_map_projection]
  have hc := congrArg (fun f => f.left ≫ pullback.fst M.hom p) (ReducedCorrespondence.IsogenyQuotient.modelTarget_comp p M e C).symm
  exact hc.trans (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient
