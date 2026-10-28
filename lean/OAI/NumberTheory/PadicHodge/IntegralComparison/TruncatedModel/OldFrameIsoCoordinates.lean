import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactIsoCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech

/-! # Old Frame Iso Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OldFrameIsoCoordinates.Morphism

noncomputable section

/-! The small-cover coefficient isomorphisms with the original frame
complex as their homology target, before choosing a resolution. -/
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

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

omit [IsSeparated Y.hom] in
theorem source_comparison (q : ℕ) :
    (show _ ⟶ (FrameCech.Complexes.source p k n X Y f hp).homology q
      from (MorphismIntrinsicHomology.Intrinsic.sourceIso p k n f hp q).hom) =
    (show _ ⟶ (FrameCech.Complexes.source p k n X Y f hp).homology q
      from (SourceExactIsoCoordinates.Morphism.homologyIso p k n f hp q).hom) :=
  SourceExactIsoCoordinates.Morphism.comparison p k n f hp q

omit [IsSeparated Y.hom] in
theorem target_comparison (q : ℕ) :
    (show _ ⟶ (FrameCech.Complexes.source p k n X Y f hp).homology q
      from (MorphismIntrinsicHomology.Intrinsic.targetIso p k n f hp q).hom) =
    (show _ ⟶ (FrameCech.Complexes.source p k n X Y f hp).homology q
      from (MorphismTargetIsoCoordinates.homologyIso p k n f hp q).hom) :=
  MorphismTargetIsoCoordinates.comparison p k n f hp q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OldFrameIsoCoordinates.Morphism
