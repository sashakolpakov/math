import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoverCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicComparisonSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Coordinates

/-! # Morphism Geometric -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometric

noncomputable section

/-! The original common-cover comparison, before imposing naturality
for a geometric pullback. The maps retain their original definitions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "U" => ModuleCat.restrictScalars (algebraMap (WittVector p k) R)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoverCoordinates.sourceNative p k n u
local notation "L₁" => Functor.obj
  (Functor.mapHomologicalComplex U (ComplexShape.up ℕ)) K₁

namespace TruncatedModelMorphismGeometricHomology

def comparison (i : ℕ) :=
  (G).map (HomologicalComplex.homologyMap
    (MorphismCoverCoordinates.sourceIso p k n u).inv i) ≫
      MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ i

end TruncatedModelMorphismGeometricHomology

namespace TruncatedModelMorphismGeometricAdditive

def comparison (i : ℕ) : (K₁).homology i →+
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y₁) n i :=
  (TruncatedModelMorphismGeometricHomology.comparison p k n u f₁ hp₁ I₁ i).hom.toAddMonoidHom.comp
    ((Witt.CoefficientCoordinates.addEquiv p k ((L₁).homology i)).toAddMonoidHom.comp
      (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso U K₁ i).toLinearEquiv.toAddEquiv.symm.toAddMonoidHom)

end TruncatedModelMorphismGeometricAdditive

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometric
