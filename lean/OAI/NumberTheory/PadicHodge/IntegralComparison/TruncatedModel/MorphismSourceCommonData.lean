import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CommonReferenceIsoCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonIsoCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechHomology

/-! # Morphism Source Common Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceCommonData

noncomputable section

/-! The checked native frame factor and coefficient isomorphism composed
in the original homology coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap
namespace Coordinates

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

abbrev original_first (q : ℕ) := Witt.ReferenceCechHomology.Reference.comparison p k
  (MorphismCover.pairs p k n u)
  (K := MorphismNewFrameCoordinates.Raw.sourceCoefficients p k n u f₁ hp₁)
  (L := MorphismNewFrameCoordinates.Raw.targetCoefficients p k n u f₁ I₁)
  (MorphismNewFrameCoordinates.Raw.coefficientMap p k n u f₁ hp₁ I₁) q
  (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
  (MorphismNewFrameData.RawCoordinates.named_first p k n u f₁ hp₁ I₁ q)

omit [IsSeparated Y₁.hom] in
theorem frame_comparison (q : ℕ) :
    (show _ ⟶ (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q
      from (MorphismIntrinsicHomology.Intrinsic.commonSourceIso p k n u f₁ hp₁ q).hom) =
    (show _ ⟶ (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q
      from (MorphismCommonIsoCoordinates.homologyIso p k n u f₁ hp₁ q).hom) :=
  MorphismCommonIsoCoordinates.comparison p k n u f₁ hp₁ q

abbrev common_comparison (q : ℕ) := Witt.ReferenceCechHomology.Reference.coefficient_comparison p k
  (MorphismCover.pairs p k n u)
  (K := MorphismNewFrameCoordinates.Raw.sourceCoefficients p k n u f₁ hp₁)
  (L := MorphismNewFrameCoordinates.Raw.targetCoefficients p k n u f₁ I₁)
  (MorphismNewFrameCoordinates.Raw.coefficientMap p k n u f₁ hp₁ I₁) q
  (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
  (MorphismNewFrameData.RawCoordinates.named_first p k n u f₁ hp₁ I₁ q)
  (CommonReferenceIsoCoordinates.MorphismReference.nativeHom p k n u f₁ hp₁ q)
  (CommonReferenceIsoCoordinates.MorphismReference.ordinaryHom p k n u f₁ hp₁ q)
  (CommonReferenceIsoCoordinates.MorphismReference.native_ordinary p k n u f₁ hp₁ q)

end Coordinates

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceCommonData
