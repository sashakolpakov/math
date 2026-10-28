import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechCoefficientComposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TargetCommonReferenceCoordinates

/-! # Intrinsic Target Common Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetCommonCoordinates.MorphismIntrinsic

noncomputable section

/-! The common-cover factor with the original target comparison's coefficient
isomorphism and explicitly typed homology map. -/

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

def output (q : ℕ) :
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y₁) n q)

variable
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def statement (q : ℕ) : Prop :=
  MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q =
    Witt.IntrinsicCechCoefficientComposite.Intrinsic.composite p k
      (MorphismCover.pairs p k n u)
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
      (MorphismCommonIsoCoordinates.source p k n u)
      (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
        ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙
          FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁))
      (L := MorphismCommonGlobal.sourceSections p k n u f₁ I₁)
      (TargetCommonIsoCoordinates.Morphism.iso p k n u f₁ hp₁)
      (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
      q (T := output p k n (Y₁ := Y₁) q)
      (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)

theorem comparison (q : ℕ) : statement p k n u f₁ hp₁ I₁ q := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetCommonCoordinates.MorphismIntrinsic
