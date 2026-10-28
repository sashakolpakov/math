import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechComposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementLeft

/-! # Intrinsic Source Old Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceOldCoordinates.MorphismIntrinsic

noncomputable section

/-! The original small-cover comparison in native coefficient and abelian
homology coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
variable (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def statement (q : ℕ) : Prop :=
  (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f hp I q).hom =
    Witt.IntrinsicCechComposite.Intrinsic.composite p k (CechSliceResolution.opens p k n X)
      (MorphismRawEq.OldFrameCoordinates.coefficientMap p k n f hp I) q
      (MorphismIntrinsicHomology.Intrinsic.sourceIso p k n f hp q).hom
      (GlobalEdge.InjectiveCech.homologyIso p k n X Y f I q).hom

theorem comparison (q : ℕ) : statement p k n f hp I q := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceOldCoordinates.MorphismIntrinsic
