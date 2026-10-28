import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TargetCommonIsoCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoefficientComposite

/-! # Target Common Reference Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TargetCommonReferenceIso.MorphismReferenceCoordinates

noncomputable section

/-! The target comparison's common-cover coefficient isomorphism in the original
module-category instances, fixed before a resolution is chosen. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

def homologyIso (q : ℕ) := ModuleCech.CoefficientComposite.coefficientIso
  (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (WittVector p k)
  (MorphismCover.pairs p k n u)
  (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
  (MorphismCommonIsoCoordinates.source p k n u)
  (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙
      FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁))
  (TargetCommonIsoCoordinates.Morphism.iso p k n u f₁ hp₁) q

omit [IsSeparated Y₁.hom] in
theorem comparison (q : ℕ) :
    (show _ ⟶ (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q
      from (MorphismIntrinsicHomology.Intrinsic.commonSourceIso p k n u f₁ hp₁ q).hom) =
    (show _ ⟶ (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q
      from (homologyIso p k n u f₁ hp₁ q).hom) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TargetCommonReferenceIso.MorphismReferenceCoordinates
