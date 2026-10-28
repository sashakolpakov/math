import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinementCohomology

/-! # Small Coefficient One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne

noncomputable section

/-! The original native p-adic coefficient comparison preserves
the actual refinement and geometric maps on H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u)
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))

def sourceSmall := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E (S ⋙ Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X₁ n)
def targetSmall := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E (T ⋙ Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X₂ n)
def sourceBig := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E (S ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n)
def targetBig := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E (T ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n)

def sourceIso := ExactHomology.ExactHomologyComparison.iso F (.up ℕ) (sourceSmall p u n) (sourceBig p u n)
  (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.sourceIso p u n) 1
def targetIso := ExactHomology.ExactHomologyComparison.iso F (.up ℕ) (targetSmall p u n) (targetBig p u n)
  (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.targetIso p u n) 1

theorem source : (F).map (HomologicalComplex.homologyMap
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) 1) ≫ (sourceIso p u n).hom =
      (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₁ n).hom ≫
        HomologicalComplex.homologyMap (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceBigRefinement p u n) 1 :=
  ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.iso p X₁ n)
    (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.sourceIso p u n)
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceBigRefinement p u n)
    (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.source p u n) 1

theorem target : (F).map (HomologicalComplex.homologyMap
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) 1) ≫ (targetIso p u n).hom =
      (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₂ n).hom ≫
        HomologicalComplex.homologyMap (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetBigRefinement p u n) 1 :=
  ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.iso p X₂ n)
    (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.targetIso p u n)
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetBigRefinement p u n)
    (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.target p u n) 1

def geometricSmallCochain : targetSmall p u n ⟶ sourceSmall p u n :=
  QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n
def geometricBigCochain : targetBig p u n ⟶ sourceBig p u n :=
  CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.geometricBigMap p u n

def geometricSmallMap := HomologicalComplex.homologyMap (geometricSmallCochain p u n) 1
def geometricBigMap := HomologicalComplex.homologyMap (geometricBigCochain p u n) 1

theorem naturality : (F).map (geometricSmallMap p u n) ≫ (sourceIso p u n).hom =
    (targetIso p u n).hom ≫ geometricBigMap p u n :=
  ExactHomology.ExactHomologyComparison.naturality F (.up ℕ)
    (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.targetIso p u n) (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.sourceIso p u n)
    (geometricSmallCochain p u n) (geometricBigCochain p u n)
    (SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient.naturality p u n) 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne
