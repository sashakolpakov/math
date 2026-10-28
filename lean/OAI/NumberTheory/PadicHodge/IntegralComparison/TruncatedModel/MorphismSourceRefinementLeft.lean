import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementData

/-! # Morphism Source Refinement Left -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementLeft

noncomputable section

/-! The complete old-cover factor in the original source comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def leftStatement (q : ℕ) : Prop :=
  (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f hp I q).hom =
    Witt.ReferenceCechComposite.Reference.composite.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (CechSliceResolution.opens p k n X)
      (MorphismRawEq.OldFrameCoordinates.coefficientMap p k n f hp I) q
      (SourceExactIsoCoordinates.Morphism.homologyIso p k n f hp q).hom
      (GlobalEdge.InjectiveCech.homologyIso p k n X Y f I q).hom

theorem left_coordinates (q : ℕ) : leftStatement p k n f hp I q := by
  unfold leftStatement
  dsimp only [MorphismIntrinsicBase.IntrinsicComparison.sourceIso, Iso.trans_hom]
  exact MorphismSourceOldCoordinates.comparison p k n f hp I q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementLeft
