import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverGlobalValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover

/-! # Top Cover Positive Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverPositiveValue

noncomputable section

/-! The native global value on an arbitrary affine cover at any
positive degree, with the original positive-degree cover coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem iso_unit {A B : AddCommGrpCat.{u}} (e : A ≅ B) (s : ℤˣ) (x : B) :
    e.hom (s • e.inv x) = s • x := by
  change e.hom.hom ((s : ℤ) • e.inv x) = (s : ℤ) • x
  rw [map_zsmul]
  exact congrArg (fun y => (s : ℤ) • y) (ConcreteCategory.congr_hom e.inv_hom_id x)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (hg : 0 < g)
  {ι : Type} [LinearOrder ι] (U : ι → X.left.Opens)
  (hU : iSup U = ⊤) (haU : ∀ j, IsAffineOpen (U j))

abbrev smallCover := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X
abbrev form := TopCover.form p k n X g

local instance form_qc : (form p k n X g).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g

abbrev smallAffine (j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X) :
    IsAffineOpen (smallCover p k n X j) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X j).property

def smallCoordinates := ModuleCech.PositiveCover.Comparison.iso (Truncated.Witt.Ring p k n) X
  U (smallCover p k n X) hU (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X)
  haU (smallAffine p k n X) (form p k n X g) g hg

theorem value (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U g) :
    ModelTopCoverComparison.globalInput p k n X Y f hp I g U hU
      (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).inv
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I (g+g)
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (smallCover p k n X) g
            ((smallCoordinates p k n X g hg U hU haU).hom x))) := by
  cases g with
  | zero => exact (Nat.lt_irrefl 0 hg).elim
  | succ r =>
      have h := TopCoverGlobalValue.value p k n X Y f hp I r U hU haU x
      dsimp only [TopCoverGlobalValue.smallCoordinates] at h
      dsimp only [smallCoordinates, ModuleCech.PositiveCover.Comparison.iso]
      with_reducible exact h

theorem bounded_value (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U g) :
    (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom
      (ModelTopCoverComparison.globalInput p k n X Y f hp I g U hU
        (ULift.up.{2,1} (ULift.up.{1,0} x))) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I (g+g)
        (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (smallCover p k n X) g
          ((smallCoordinates p k n X g hg U hU haU).hom x)) := by
  rw [value p k n X Y f hp I g hg U hU haU x]
  exact iso_unit _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverPositiveValue
