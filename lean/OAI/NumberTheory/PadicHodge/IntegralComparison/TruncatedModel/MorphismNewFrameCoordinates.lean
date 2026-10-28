import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CechTotalMapFactorization

/-! # Morphism New Frame Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameCoordinates.Raw

noncomputable section

/-! The original common-source frame comparison expressed through
its literal presheaf-total map, with the map equality transported first. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

abbrev sourceCoefficients : CochainComplex
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      (FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁)))

abbrev targetCoefficients : CochainComplex
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
      (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)).mapHomologicalComplex (.up ℕ)).obj
    (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁))

def coefficientMap : sourceCoefficients p k n u f₁ hp₁ ⟶
    targetCoefficients p k n u f₁ I₁ :=
  MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁

abbrev new_first (q : ℕ) := Witt.CechTotalMapFactorization.comparison p k
  (MorphismCover.pairs p k n u)
  (K := sourceCoefficients p k n u f₁ hp₁)
  (L := targetCoefficients p k n u f₁ I₁)
  (coefficientMap p k n u f₁ hp₁ I₁) q
  (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
  (MorphismNewFrameData.RawCoordinates.named_first p k n u f₁ hp₁ I₁ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameCoordinates.Raw
