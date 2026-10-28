import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.InverseSquare

/-! # Small Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient

noncomputable section

/-! The original small p-adic coefficient comparison preserves
actual common-cover refinement and geometric pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "G" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p) (ComplexShape.up ℕ)
local notation "Q" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))) (ComplexShape.up ℕ)
local notation "F" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p) (ComplexShape.up ℕ)

def sourceIso := (G).mapIso (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceIso p u n).symm ≪≫
  CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceIso p u n
def targetIso := (G).mapIso (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetIso p u n).symm ≪≫
  CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetIso p u n
def sourceOldIso := Coefficient.IntrinsicPadicSmallQuotientTotal.coefficientTotalIso p X₁ n ≪≫
  IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X₁ n
def targetOldIso := Coefficient.IntrinsicPadicSmallQuotientTotal.coefficientTotalIso p X₂ n ≪≫
  IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X₂ n

theorem source_inverse : (F).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) ≫
    (G).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceIso p u n).inv =
      (G).map (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X₁ n).inv ≫
        (G).map (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceRefinement p u n) :=
  GeometricComparison.Functor.InverseSquare.FunctorInverseSquare.square G (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X₁ n)
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceIso p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceRefinement p u n)
    ((Q).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n))
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.source p u n)

theorem source : (F).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) ≫
    (sourceIso p u n).hom = (sourceOldIso p (X₁ := X₁) n).hom ≫
      CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.sourceBigRefinement p u n :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (source_inverse p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.source p u n)

theorem target_inverse : (F).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) ≫
    (G).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetIso p u n).inv =
      (G).map (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X₂ n).inv ≫
        (G).map (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetRefinement p u n) :=
  GeometricComparison.Functor.InverseSquare.FunctorInverseSquare.square G (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X₂ n)
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetIso p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetRefinement p u n)
    ((Q).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n))
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.target p u n)

theorem target : (F).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) ≫
    (targetIso p u n).hom = (targetOldIso p (X₂ := X₂) n).hom ≫
      CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.targetBigRefinement p u n :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (target_inverse p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.target p u n)

theorem geometric_inverse : (F).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n) ≫
    (G).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceIso p u n).inv =
      (G).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetIso p u n).inv ≫
        (G).map (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.geometricMap p u n) :=
  GeometricComparison.Functor.InverseSquare.FunctorInverseSquare.square G (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetIso p u n)
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceIso p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.geometricMap p u n)
    ((Q).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n))
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.naturality p u n)

theorem naturality : (F).map (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n) ≫
    (sourceIso p u n).hom = (targetIso p u n).hom ≫
      CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.geometricBigMap p u n :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (geometric_inverse p u n)
    (CoefficientRefinement.IntrinsicPadicGeometricCoefficientRefinement.naturality p u n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficient.IntrinsicPadicGeometricSmallCoefficient
