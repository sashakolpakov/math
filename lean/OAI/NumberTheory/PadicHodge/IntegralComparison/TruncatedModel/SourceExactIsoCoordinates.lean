import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetIsoCoordinates

/-! # Source Exact Iso Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactIsoCoordinates.Morphism

noncomputable section

/-! The native source coefficient isomorphism with the original source
coordinate map and its presheaf-total target fixed before homology. -/
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

def iso :
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj
      (MorphismTargetIsoCoordinates.source p k n (X := X)) ≅
        MorphismTargetIsoCoordinates.target p k n f hp :=
  MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f hp

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def homologyIso (q : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso
  (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) (.up ℕ)
  (MorphismTargetIsoCoordinates.source p k n (X := X))
  (MorphismTargetIsoCoordinates.target p k n f hp) (iso p k n f hp) q

omit [IsSeparated Y.hom] in
theorem comparison (q : ℕ) :
    (MorphismIntrinsicHomology.Intrinsic.sourceIso p k n f hp q).hom =
      (homologyIso p k n f hp q).hom := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactIsoCoordinates.Morphism
