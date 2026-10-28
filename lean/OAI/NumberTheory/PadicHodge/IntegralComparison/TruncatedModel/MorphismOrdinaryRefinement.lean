import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryCechCoordinates

/-! # Morphism Ordinary Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryRefinement.Ordinary

noncomputable section

/-! The ordinary-to-crystalline coordinate isomorphisms commute with
the actual source and target refinements to the common affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem map_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' D' : C}
    (a : A ⟶ B) (b : B ⟶ D') (c : A ⟶ C') (d : C' ⟶ D')
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

private theorem paste {C : Type*} [Category* C] {P Q R S T U : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (d : P ⟶ T)
    (e : T ⟶ U) (f : U ⟶ S) (g : Q ⟶ U)
    (h₁ : a ≫ g = d ≫ e) (h₂ : g ≫ f = b ≫ c) :
    (a ≫ b) ≫ c = d ≫ (e ≫ f) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => a ≫ z) h₂.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ f) h₁).trans (Category.assoc _ _ _))))

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
local notation "V₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X₁
local notation "V₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X₂

def sourceCoordinates := GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso (NonemptyCechNerve.nerve V₁)
  (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁).symm

def targetCoordinates := GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso (NonemptyCechNerve.nerve V₂)
  (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂).symm

def sourceChosenIso := (GC).mapIso (sourceCoordinates p k n f₁ hp₁) ≪≫
  MorphismCoefficientCech.sourceChosenIso p k n f₁ hp₁

def targetChosenIso := (GC).mapIso (targetCoordinates p k n f₂ hp₂) ≪≫
  MorphismCoefficientCech.targetChosenIso p k n f₂ hp₂

abbrev source_coordinate_square := map_square GC
  (sourceCoordinates p k n f₁ hp₁).hom
  (MorphismOrdinaryCech.Ordinary.sourceFrameRefinement p k n u f₁ hp₁)
  (MorphismOrdinaryCech.Ordinary.sourceOrdinaryRefinement p k n u)
  (MorphismOrdinaryCech.Ordinary.sourceIso p k n u f₁ hp₁).hom
  (MorphismOrdinaryCech.Ordinary.source p k n u f₁ hp₁)

abbrev target_coordinate_square := map_square GC
  (targetCoordinates p k n f₂ hp₂).hom
  (MorphismOrdinaryCech.Ordinary.targetFrameRefinement p k n u f₂ hp₂)
  (MorphismOrdinaryCech.Ordinary.targetOrdinaryRefinement p k n u)
  (MorphismOrdinaryCech.Ordinary.targetIso p k n u f₂ hp₂).hom
  (MorphismOrdinaryCech.Ordinary.target p k n u f₂ hp₂)

abbrev source := paste
  ((GC).map (sourceCoordinates p k n f₁ hp₁).hom)
  (MorphismCoefficientCech.sourceChosenIso p k n f₁ hp₁).hom
  (MorphismCoefficientCech.sourceRefinement p k n u f₁ hp₁)
  ((GC).map (MorphismOrdinaryCech.Ordinary.sourceOrdinaryRefinement p k n u))
  ((GC).map (MorphismOrdinaryCech.Ordinary.sourceIso p k n u f₁ hp₁).hom)
  (MorphismCoefficientCech.sourceIso p k n u f₁ hp₁).hom
  ((GC).map (MorphismOrdinaryCech.Ordinary.sourceFrameRefinement p k n u f₁ hp₁))
  (source_coordinate_square p k n u f₁ hp₁)
  (MorphismCoefficientCech.source p k n u f₁ hp₁)

abbrev target := paste
  ((GC).map (targetCoordinates p k n f₂ hp₂).hom)
  (MorphismCoefficientCech.targetChosenIso p k n f₂ hp₂).hom
  (MorphismCoefficientCech.targetRefinement p k n u f₂ hp₂)
  ((GC).map (MorphismOrdinaryCech.Ordinary.targetOrdinaryRefinement p k n u))
  ((GC).map (MorphismOrdinaryCech.Ordinary.targetIso p k n u f₂ hp₂).hom)
  (MorphismCoefficientCech.targetIso p k n u f₂ hp₂).hom
  ((GC).map (MorphismOrdinaryCech.Ordinary.targetFrameRefinement p k n u f₂ hp₂))
  (target_coordinate_square p k n u f₂ hp₂)
  (MorphismCoefficientCech.target p k n u f₂ hp₂)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryRefinement.Ordinary
