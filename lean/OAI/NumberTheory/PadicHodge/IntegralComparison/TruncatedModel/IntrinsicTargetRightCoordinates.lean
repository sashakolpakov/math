import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetCommonCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceData

/-! # Intrinsic Target Right Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetRightCoordinates.MorphismIntrinsic

noncomputable section

/-! The original two homology prefixes applied to the native common-cover
comparison, with the source homology type fixed before the resolution. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalHomology {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex C c) (q : ι) : C :=
  K.homology q

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def statement (i : ℕ) : Prop :=
  @Eq (@Quiver.Hom
      (@ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring)
      (@ModuleCat.moduleCategory
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) ULift.ring).toQuiver
      ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).obj
        (@originalHomology (ModuleCat.{0} (WittVector p k))
          (@ModuleCat.moduleCategory (WittVector p k) (WittVector.instCommRing p k).toRing)
          (@ModuleCat.abelian (WittVector p k) (WittVector.instCommRing p k).toRing)
          ℕ (ComplexShape.up ℕ)
          (((ModuleCat.restrictScalars
            (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))).mapHomologicalComplex
              (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X₂)) i))
      (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
          (J := Ideal.span {(p : WittVector p k)})
          (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
          (Witt.Crystalline.wittStructureMap p k Y₁) n i)))
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫
    MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ i)
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫
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
      i (T := IntrinsicTargetCommonCoordinates.MorphismIntrinsic.output p k n (Y₁ := Y₁) i)
      (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ i))

theorem comparison (i : ℕ) : statement p k n u f₁ hp₁ I₁ i := by
  unfold statement
  have h := IntrinsicTargetCommonCoordinates.MorphismIntrinsic.comparison
    p k n u f₁ hp₁ I₁ i
  change _ at h
  delta IntrinsicTargetCommonCoordinates.MorphismIntrinsic.statement at h
  exact congrArg
    (fun c =>
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫ c)
    h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetRightCoordinates.MorphismIntrinsic
