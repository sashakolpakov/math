import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechCoefficientComposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementData

/-! # Intrinsic Source Common Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceCommonCoordinates.MorphismIntrinsic

/-! The original common-cover comparison in native coefficient and
Čech homology coordinates, with its bounded output fixed explicitly. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]

variable (n : ℕ)
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

def statement (q : ℕ) : Prop :=
  MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q =
    Witt.IntrinsicCechCoefficientComposite.Intrinsic.composite p k (MorphismCover.pairs p k n u)
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
      (MorphismCommonIsoCoordinates.source p k n u)
      (K := MorphismNewFrameCoordinates.Raw.sourceCoefficients p k n u f₁ hp₁)
      (L := MorphismNewFrameCoordinates.Raw.targetCoefficients p k n u f₁ I₁)
      (MorphismCommonIsoCoordinates.iso p k n u f₁ hp₁)
      (MorphismNewFrameCoordinates.Raw.coefficientMap p k n u f₁ hp₁ I₁)
      q (T := output p k n (Y₁ := Y₁) q)
      (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)

theorem comparison (q : ℕ) : statement p k n u f₁ hp₁ I₁ q :=
  MorphismSourceRefinementData.common_comparison p k n u f₁ hp₁ I₁ q

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceCommonCoordinates.MorphismIntrinsic

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceCommonCoordinates.MorphismIntrinsicRight

/-! The common-cover factor of source refinement in native coefficient
coordinates, with the original homology map fixed on both sides. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

private def originalHomology {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex C c) (q : ι) : C :=
  K.homology q

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]

variable (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

variable
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

def statement (q : ℕ) : Prop :=
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
              (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X₁)) q))
      (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
          (J := Ideal.span {(p : WittVector p k)})
          (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
          (Witt.Crystalline.wittStructureMap p k Y₁) n q)))
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u) q) ≫
    MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q)
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u) q) ≫
    Witt.IntrinsicCechCoefficientComposite.Intrinsic.composite p k (MorphismCover.pairs p k n u)
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
      (MorphismCommonIsoCoordinates.source p k n u)
      (K := MorphismNewFrameCoordinates.Raw.sourceCoefficients p k n u f₁ hp₁)
      (L := MorphismNewFrameCoordinates.Raw.targetCoefficients p k n u f₁ I₁)
      (MorphismCommonIsoCoordinates.iso p k n u f₁ hp₁)
      (MorphismNewFrameCoordinates.Raw.coefficientMap p k n u f₁ hp₁ I₁)
      q (T := MorphismIntrinsic.output p k n (Y₁ := Y₁) q)
      (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q))

theorem comparison (q : ℕ) : statement p k n u f₁ hp₁ I₁ q := by
  unfold statement
  have h := MorphismIntrinsic.comparison
    p k n u f₁ hp₁ I₁ q
  change _ at h
  delta MorphismIntrinsic.statement at h
  exact congrArg
    (fun c =>
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u) q) ≫ c)
    h

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceCommonCoordinates.MorphismIntrinsicRight

end

end OAI
