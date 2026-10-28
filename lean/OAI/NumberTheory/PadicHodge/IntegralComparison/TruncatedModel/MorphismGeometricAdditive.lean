import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Coordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RestrictedHomologyCoordinates

/-! # Morphism Geometric Additive -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricAdditive

noncomputable section

/-! The actual geometric pullback to the common affine cover agrees
with bounded crystalline pullback on the original additive groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
    (Witt.Crystalline.wittStructureMap p k Y₂) n)) (i : ℕ)

private abbrev inverse_natural :=
  Witt.RestrictedHomologyCoordinates.inverse_natural p k
    (Truncated.Witt.Ring p k n)
    (MorphismGeometricCoordinates.map p k n u) i

omit [Fintype k] [CharP k p] [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem coordinates_natural
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X₂).homology i) :
    (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))) (MorphismCoverCoordinates.sourceNative p k n u) i).inv (HomologicalComplex.homologyMap (MorphismGeometricCoordinates.map p k n u) i x) =
      HomologicalComplex.homologyMap ((((ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)))).mapHomologicalComplex (.up ℕ)).map (MorphismGeometricCoordinates.map p k n u)) i
        ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))) (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X₂) i).inv x) :=
  inverse_natural p k n u i x

include sq in
theorem naturality
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X₂).homology i) :
    MorphismGeometric.TruncatedModelMorphismGeometricAdditive.comparison p k n u f₁ hp₁ I₁ i (HomologicalComplex.homologyMap (MorphismGeometricCoordinates.map p k n u) i x) =
      BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X₂ Y₂ f₂ hp₂ I₂ i x) := by
  exact (Witt.RestrictedHomologyCoordinates.comparison p k
    (Truncated.Witt.Ring p k n)
    (MorphismGeometricCoordinates.map p k n u) i
    (MorphismGeometric.TruncatedModelMorphismGeometricHomology.comparison p k n u f₁ hp₁ I₁ i)
    ((MorphismIntrinsicBase.IntrinsicComparison.targetIso p k n f₂ hp₂ I₂ i).hom ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i))
    (MorphismGeometricHomology.naturality p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i) x).trans
      (congrArg (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i)
        (Coordinates.Comparison.comparison_apply
          p k n X₂ Y₂ f₂ hp₂ I₂ i x).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricAdditive
