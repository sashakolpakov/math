import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceClassBaseChange

/-! # Difference Fiber Triviality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberTriviality.Geometric

noncomputable section

/-! Homogeneity on an actual field fiber makes the restriction of the
original normalized difference bundle trivial on the entire fiber square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem relativeDifference_total_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) =
      RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
        (fst A.scheme A.scheme) (snd A.scheme A.scheme) := by
  have h := DifferenceClassBaseChange.Geometric.relativeDifference_pair_class A L (fst A.scheme A.scheme) (snd A.scheme A.scheme)
  rw [lift_fst_snd] at h
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (A.scheme ⊗ A.scheme).left)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) = _ at h
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _).symm.trans h

theorem difference_fieldFiber_trivial_of_homogeneous
    {k : Type} [Field k] (f : Spec (.of k) ⟶ S)
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (A.pullback f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst A.scheme.hom f)))) :
    Nonempty (((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
      (pullback.fst (A.scheme ⊗ A.scheme).hom f)).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback f).obj (A.scheme ⊗ A.scheme)).left) := by
  let M := L.pullback (pullback.fst A.scheme.hom f)
  have hn : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M :=
    RelativeNormalizationFibers.Geometric.identityNormalizedLine_fieldPullback_class A L (pullback.fst A.scheme.hom f)
      (pullback.snd A.scheme.hom f) f pullback.condition
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback
      (pullback.fst (A.scheme ⊗ A.scheme).hom f)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback f).obj (A.scheme ⊗ A.scheme)).left := by
    calc
      _ = RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (A.scheme ⊗ A.scheme).hom f)
          (RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L))
            (fst A.scheme A.scheme) (snd A.scheme A.scheme)) :=
        congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst (A.scheme ⊗ A.scheme).hom f))
          (relativeDifference_total_class A L)
      _ = RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass (A.pullback f).scheme
          (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst A.scheme.hom f) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)))
          ((Over.pullback f).map (fst A.scheme A.scheme))
          ((Over.pullback f).map (snd A.scheme A.scheme)) :=
        DifferenceClassBaseChange.Geometric.groupDifferenceClass_baseChange A _ f _ _
      _ = 1 := by
        rw [hn]
        exact DifferenceClassBaseChange.Geometric.homogeneousLine_groupDifference (A.pullback f) M hL _ _
  exact Quotient.exact hc

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceFiberTriviality.Geometric
