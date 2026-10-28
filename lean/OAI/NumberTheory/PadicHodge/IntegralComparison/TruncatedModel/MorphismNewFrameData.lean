import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TypedCechMapCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapFactorization

/-! # Morphism New Frame Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameData.RawCoordinates

noncomputable section

/-! The original common-source frame comparison expressed through
its literal presheaf-total map, with the map equality transported first. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem replace_first {C : Type*} [Category C] {A B T : C}
    (b : B ⟶ T) {f : A ⟶ T} {a a' : A ⟶ B}
    (h : f = a ≫ b) (ha : a = a') : f = a' ≫ b :=
  h.trans (congrArg (fun x => x ≫ b) ha)

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

abbrev named_map :=
  TypedCechMapCoordinates.MorphismNew.comparison p k n u f₁ hp₁ I₁

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

abbrev named_homology (q : ℕ) :=
  congrArg
    (fun (a : MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁ ⟶
        MorphismFrameTypedMaps.Homology.sourceInjectiveNew p k n u f₁ I₁) =>
      homologyMap a q)
    (named_map p k n u f₁ hp₁ I₁)

abbrev named_first (q : ℕ) := replace_first
  (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
  (MorphismNewFrameHomology.Raw.reverse p k n u f₁ hp₁ I₁ q).symm
  (named_homology p k n u f₁ hp₁ I₁ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameData.RawCoordinates
