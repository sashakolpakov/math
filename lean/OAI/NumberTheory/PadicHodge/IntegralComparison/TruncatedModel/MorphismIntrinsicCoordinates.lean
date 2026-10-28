import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryRefinement

/-! # Morphism Intrinsic Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicCoordinates.Intrinsic

noncomputable section

/-! The native small de Rham totals retain the actual common-cover
refinement identities under their ordinary and PD coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem precompose {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {P Q R : C} {S T : D}
    (a : P ⟶ Q) (b : Q ⟶ R) (x : F.obj Q ⟶ S) (y : S ⟶ T) (z : F.obj R ⟶ T)
    (h : x ≫ y = F.map b ≫ z) :
    (F.map a ≫ x) ≫ y = F.map (a ≫ b) ≫ z :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => F.map a ≫ t) h).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ z) (F.map_comp a b).symm)))

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "GC" => Functor.mapHomologicalComplex G (ComplexShape.up ℕ)

def sourceIso := (GC).mapIso (OrdinaryCechCoordinates.Ordinary.iso p k n X₁) ≪≫
  MorphismOrdinaryRefinement.Ordinary.sourceChosenIso p k n f₁ hp₁

def targetIso := (GC).mapIso (OrdinaryCechCoordinates.Ordinary.iso p k n X₂) ≪≫
  MorphismOrdinaryRefinement.Ordinary.targetChosenIso p k n f₂ hp₂

def sourceMap := (OrdinaryCechCoordinates.Ordinary.iso p k n X₁).hom ≫
  MorphismOrdinaryCech.Ordinary.sourceOrdinaryRefinement p k n u

def targetMap := (OrdinaryCechCoordinates.Ordinary.iso p k n X₂).hom ≫
  MorphismOrdinaryCech.Ordinary.targetOrdinaryRefinement p k n u

abbrev source := precompose GC
  (OrdinaryCechCoordinates.Ordinary.iso p k n X₁).hom
  (MorphismOrdinaryCech.Ordinary.sourceOrdinaryRefinement p k n u)
  (MorphismOrdinaryRefinement.Ordinary.sourceChosenIso p k n f₁ hp₁).hom
  (MorphismCoefficientCech.sourceRefinement p k n u f₁ hp₁)
  (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁).hom
  (MorphismOrdinaryRefinement.Ordinary.source p k n u f₁ hp₁)

abbrev target := precompose GC
  (OrdinaryCechCoordinates.Ordinary.iso p k n X₂).hom
  (MorphismOrdinaryCech.Ordinary.targetOrdinaryRefinement p k n u)
  (MorphismOrdinaryRefinement.Ordinary.targetChosenIso p k n f₂ hp₂).hom
  (MorphismCoefficientCech.targetRefinement p k n u f₂ hp₂)
  (MorphismCoefficientCech.ordinaryTargetIso p k n u f₂ hp₂).hom
  (MorphismOrdinaryRefinement.Ordinary.target p k n u f₂ hp₂)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicCoordinates.Intrinsic
