import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyIsoNaturality

/-! # Morphism Ordinary Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryCech.Ordinary

noncomputable section

/-! Ordinary de Rham and PD-frame Čech totals have the same actual
model pullbacks and the same common-cover refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
local notation "O₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso.Ordinary.target p k n X₁
local notation "O₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso.Ordinary.target p k n X₂
local notation "P₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.pdComplexes p k n X₁ Y₁ f₁ hp₁
local notation "P₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.pdComplexes p k n X₂ Y₂ f₂ hp₂
local notation "V₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X₁
local notation "V₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n) X₂
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.source p k n u
local notation "r₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRefinement.target p k n u

def sourceOrdinaryRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₁ U V₁ r₁
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) O₁)

def targetOrdinaryRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₂ U V₂ r₂
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) O₂)

def sourceFrameRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₁ U V₁ r₁
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P₁)

def targetFrameRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₂ U V₂ r₂
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P₂)

def sourceIso := GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E
  (Functor.isoWhiskerLeft (Functor.op F₁)
    (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁).symm)

def targetIso := GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso E
  (Functor.isoWhiskerLeft (Functor.op F₂)
    (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂).symm)

theorem source :
    (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso (NonemptyCechNerve.nerve V₁)
      (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁).symm).hom ≫
        sourceFrameRefinement p k n u f₁ hp₁ =
      sourceOrdinaryRefinement p k n u ≫ (sourceIso p k n u f₁ hp₁).hom :=
  GeometricComparison.CechAssembly.RefinedIso.CechAssemblyRefinedIso.naturality F₁ U V₁ r₁
    (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁).symm

theorem target :
    (GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso (NonemptyCechNerve.nerve V₂)
      (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂).symm).hom ≫
        targetFrameRefinement p k n u f₂ hp₂ =
      targetOrdinaryRefinement p k n u ≫ (targetIso p k n u f₂ hp₂).hom :=
  GeometricComparison.CechAssembly.RefinedIso.CechAssemblyRefinedIso.naturality F₂ U V₂ r₂
    (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂).symm

def ordinaryMap := (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
  (MorphismBase.Comparison.ordinaryMap p k n u)

def frameMap := (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map
  (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)

omit [IsProper X₁.hom] [IsProper X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] in
theorem diagram_natural :
    MorphismBase.Comparison.ordinaryMap p k n u ≫
      Functor.whiskerLeft (Functor.op F₁)
        (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁).inv =
    Functor.whiskerLeft (Functor.op F₂)
        (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂).inv ≫
      MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq :=
  InverseCoordinateHomology.inverse
    (Functor.isoWhiskerLeft (Functor.op F₂) (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂))
    (Functor.isoWhiskerLeft (Functor.op F₁) (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁))
    (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismBase.Comparison.ordinaryMap p k n u)
    (MorphismBase.Comparison.natural p k n u v f₁ f₂ hp₁ hp₂ sq)

theorem natural : ordinaryMap p k n u ≫ (sourceIso p k n u f₁ hp₁).hom =
    (targetIso p k n u f₂ hp₂).hom ≫ frameMap p k n u v f₁ f₂ hp₁ hp₂ sq :=
  Cech.AssemblyIsoNaturality.inverse E
    (Functor.isoWhiskerLeft (Functor.op F₂) (OrdinaryBaseIso.Ordinary.pdIso p k n X₂ Y₂ f₂ hp₂))
    (Functor.isoWhiskerLeft (Functor.op F₁) (OrdinaryBaseIso.Ordinary.pdIso p k n X₁ Y₁ f₁ hp₁))
    (MorphismPrincipal.Comparison.frameMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismBase.Comparison.ordinaryMap p k n u)
    (MorphismBase.Comparison.natural p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOrdinaryCech.Ordinary
