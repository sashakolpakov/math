import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality

/-! # Morphism Coefficient Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientCech

noncomputable section

/-! The literal crystalline coefficient functor preserves model-frame
refinement and ordinary de Rham pullback on the common Čech cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem map_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B C' D' : C}
    (a : A ⟶ B) (b : B ⟶ D') (c : A ⟶ C') (d : C' ⟶ D')
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)
local notation "P₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.pdComplexes p k n X₁ Y₁ f₁ hp₁
local notation "P₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.pdComplexes p k n X₂ Y₂ f₂ hp₂
local notation "V₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X₁
local notation "V₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X₂
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.source p k n u
local notation "r₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.target p k n u
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "GC" => Functor.mapHomologicalComplex G (ComplexShape.up ℕ)

def sourceChosenIso := GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G (NonemptyCechNerve.nerve V₁)
  (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices V₁) P₁

def targetChosenIso := GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G (NonemptyCechNerve.nerve V₂)
  (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices V₂) P₂

def sourceIso := GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E
  (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (Functor.op F₁ ⋙ P₁)

def targetIso := GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E
  (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (Functor.op F₂ ⋙ P₂)

def sourceRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₁ U V₁ r₁
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁))

def targetRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₂ U V₂ r₂
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.source p k n X₂ Y₂ f₂ hp₂))

theorem source : (GC).map (MorphismOrdinaryCech.Ordinary.sourceFrameRefinement p k n u f₁ hp₁) ≫
    (sourceIso p k n u f₁ hp₁).hom =
    (sourceChosenIso p k n f₁ hp₁).hom ≫ sourceRefinement p k n u f₁ hp₁ :=
  GeometricComparison.CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total F₁ G U V₁ r₁ P₁

theorem target : (GC).map (MorphismOrdinaryCech.Ordinary.targetFrameRefinement p k n u f₂ hp₂) ≫
    (targetIso p k n u f₂ hp₂).hom =
    (targetChosenIso p k n f₂ hp₂).hom ≫ targetRefinement p k n u f₂ hp₂ :=
  GeometricComparison.CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient.total F₂ G U V₂ r₂ P₂

def geometricMap := (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
  (Functor.whiskerRight
    (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq) GC)

theorem natural : (GC).map
    (MorphismOrdinaryCech.Ordinary.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq) ≫
      (sourceIso p k n u f₁ hp₁).hom =
    (targetIso p k n u f₂ hp₂).hom ≫ geometricMap p k n u v f₁ f₂ hp₁ hp₂ sq :=
  GeometricComparison.CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural G E (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
    (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)

def ordinarySourceIso :=
  (GC).mapIso (MorphismOrdinaryCech.Ordinary.sourceIso p k n u f₁ hp₁) ≪≫
    sourceIso p k n u f₁ hp₁

def ordinaryTargetIso :=
  (GC).mapIso (MorphismOrdinaryCech.Ordinary.targetIso p k n u f₂ hp₂) ≪≫
    targetIso p k n u f₂ hp₂

theorem ordinary_map_square :
    (GC).map (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) ≫
      (GC).map (MorphismOrdinaryCech.Ordinary.sourceIso p k n u f₁ hp₁).hom =
    (GC).map (MorphismOrdinaryCech.Ordinary.targetIso p k n u f₂ hp₂).hom ≫
      (GC).map (MorphismOrdinaryCech.Ordinary.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq) :=
  map_square GC
    (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)
    (MorphismOrdinaryCech.Ordinary.sourceIso p k n u f₁ hp₁).hom
    (MorphismOrdinaryCech.Ordinary.targetIso p k n u f₂ hp₂).hom
    (MorphismOrdinaryCech.Ordinary.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismOrdinaryCech.Ordinary.natural p k n u v f₁ f₂ hp₁ hp₂ sq)
abbrev ordinary_natural :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (ordinary_map_square p k n u v f₁ f₂ hp₁ hp₂ sq)
    (natural p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCoefficientCech
