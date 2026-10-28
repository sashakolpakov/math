import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameCechHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapCoordinates

/-! # New Cech Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.NewCechMapCoordinates.Morphism

noncomputable section

/-! The actual common-cover frame map in the generic named Čech-total
coordinates, before applying homology or the bounded global map. -/
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

def map := ModuleCech.TotalMapCoordinates.map.{1, 2}
  (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
  (MorphismCover.pairs p k n u)
  (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)

theorem comparison :
    MorphismFrameCechHomology.sourceComparison p k n u f₁ hp₁ I₁ =
      Morphism.map p k n u f₁ hp₁ I₁ := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.NewCechMapCoordinates.Morphism
