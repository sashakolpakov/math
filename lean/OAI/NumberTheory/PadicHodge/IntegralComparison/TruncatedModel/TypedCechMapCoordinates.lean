import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.NewCechMapCoordinates

/-! # Typed Cech Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TypedCechMapCoordinates.MorphismNew

noncomputable section

/-! Identify the original typed common-source map with the named
Čech total map before taking homology. -/
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

theorem comparison :
    MorphismFrameTypedMaps.Homology.sourceNewMap p k n u f₁ hp₁ I₁ =
      NewCechMapCoordinates.Morphism.map p k n u f₁ hp₁ I₁ := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TypedCechMapCoordinates.MorphismNew
