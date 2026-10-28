import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelTopCoverComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverIntrinsicValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AffineCommonCover

/-! # Top Cover Global Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverGlobalValue

noncomputable section

/-! Any original affine-cover top class has its native crystalline
value through the actual cover-comparison isomorphism to the small cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (r : ℕ) [SmoothOfRelativeDimension (r+1) X.hom]
  {ι ν : Type} [LinearOrder ι] [LinearOrder ν]
  (U : ι → X.left.Opens) (hU : iSup U = ⊤) (haU : ∀ j, IsAffineOpen (U j))

abbrev smallCover := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X
abbrev form := TopCover.form p k n X (r+1)

local instance form_qc : (form p k n X r).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X (r+1)

abbrev smallAffine (j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    IsAffineOpen (smallCover p k n X j) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X j).property

def smallCoordinates := ModuleCech.Cover.Comparison.iso (Truncated.Witt.Ring p k n) X
  U (smallCover p k n X) hU (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X)
  haU (smallAffine p k n X) (form p k n X r) r

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension (r + 1) X.hom] in
private theorem small_input {Z : AddCommGrpCat.{2}}
    (v : (OrderedCech.Projection.complex (smallCover p k n X)
      ((TopCover.coefficients p k n X).obj (form p k n X r))).homology (r+1) ⟶ Z)
    (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
      (smallCover p k n X) (r+1)) :
    (TopCoverCoefficients.inputMap p k n X (r+1) (smallCover p k n X) ≫ v)
      (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    v (ModelAdditiveTop.coefficientMorphism p k n X (r+1)
      (ULift.up.{2,1} (ULift.up.{1,0} x))) := by
  rfl

variable (T : ν → X.left.Opens)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rSmall : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) (smallCover p k n X))
  (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))

include T rU rSmall hT haT in
theorem comparison
    (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U (r+1)) :
    ModelTopCoverComparison.globalInput p k n X Y f hp I (r+1) U hU
      (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) (r+1) (r+1) •
      (AdditiveGlobal.globalHomologyIso p k n X Y f I ((r+1)+(r+1))).inv
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I ((r+1)+(r+1))
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (smallCover p k n X) (r+1)
            ((smallCoordinates p k n X r U hU haU).hom x))) := by
  have h := ModelTopCoverComparison.cover_apply p k n X Y f hp I r U hU haU
    (smallCover p k n X) (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X)
    (smallAffine p k n X) T rU rSmall hT haT x
  have hs := TopCoverIntrinsicValue.Intrinsic.comparison p k n X Y f hp I (r+1)
    ((smallCoordinates p k n X r U hU haU).hom x)
  have hc := small_input p k n X r
    (TopCover.globalMap p k n X Y f hp I (r+1) (smallCover p k n X)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X))
    ((smallCoordinates p k n X r U hU haU).hom x)
  dsimp only [ModelTopCoverComparison.globalInput] at h
  dsimp only [smallCoordinates] at hc hs
  dsimp only [ModelTopCoverComparison.globalInput, smallCoordinates]
  with_reducible exact h.trans (hc.trans hs)

include T rU rSmall hT haT in
theorem source_comparison (c : ℕ)
    (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U (r+1)) :
    PrincipalSheafValue.globalValue p k n X Y f hp I (r+1) c U hU
      (ULift.up.{2,1} (ULift.up.{1,0}
        (SourceGlobal.sourceCoordinates p k n X (r+1) c U x))) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) (r+1) (r+1) •
      (AdditiveGlobal.globalHomologyIso p k n X Y f I ((r+1)+(r+1))).inv
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I ((r+1)+(r+1))
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (smallCover p k n X) (r+1)
            ((smallCoordinates p k n X r U hU haU).hom x))) :=
  (SourceGlobal.comparison_apply p k n X Y f hp I (r+1) c U hU x).trans
    (comparison p k n X Y f hp I r U hU haU T rU rSmall hT haT x)

theorem value
    (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U (r+1)) :
    ModelTopCoverComparison.globalInput p k n X Y f hp I (r+1) U hU
      (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) (r+1) (r+1) •
      (AdditiveGlobal.globalHomologyIso p k n X Y f I ((r+1)+(r+1))).inv
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I ((r+1)+(r+1))
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (smallCover p k n X) (r+1)
            ((smallCoordinates p k n X r U hU haU).hom x))) := by
  let : LinearOrder (ι × AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :=
    IsWellOrder.linearOrder WellOrderingRel
  have hsmall : iSup (smallCover p k n X) = ⊤ :=
    AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X
  apply comparison p k n X Y f hp I r U hU haU
    (Relative.AffineCommonCover.opens U (smallCover p k n X))
    (Relative.AffineCommonCover.left U (smallCover p k n X))
    (Relative.AffineCommonCover.right U (smallCover p k n X))
  · have h := Relative.AffineCommonCover.covers U (smallCover p k n X) ⊤ ⊤
      (by simpa only [top_inf_eq] using hU)
      (by simpa only [top_inf_eq] using hsmall)
    simpa only [top_inf_eq] using h
  · exact Relative.AffineCommonCover.affine U (smallCover p k n X) haU (smallAffine p k n X)

theorem source_value (c : ℕ)
    (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U (r+1)) :
    PrincipalSheafValue.globalValue p k n X Y f hp I (r+1) c U hU
      (ULift.up.{2,1} (ULift.up.{1,0}
        (SourceGlobal.sourceCoordinates p k n X (r+1) c U x))) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) (r+1) (r+1) •
      (AdditiveGlobal.globalHomologyIso p k n X Y f I ((r+1)+(r+1))).inv
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I ((r+1)+(r+1))
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (smallCover p k n X) (r+1)
            ((smallCoordinates p k n X r U hU haU).hom x))) :=
  (SourceGlobal.comparison_apply p k n X Y f hp I (r+1) c U hU x).trans
    (value p k n X Y f hp I r U hU haU x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverGlobalValue
