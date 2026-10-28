import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionRefinementData

/-! # Small Assembly One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallAssemblyOne.IntrinsicPadicGeometricSmallAssemblyHOne

noncomputable section

/-! Original coefficient comparison in the assembled integral
refinement coordinates used by the global comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p

theorem source : (F).map (HomologicalComplex.homologyMap
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.sourceRefinement p u n) 1) ≫
      (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.sourceIso p u n).hom =
    (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₁ n).hom ≫
      SectionRefinementData.IntrinsicPadicGeometricSectionRefinementData.sourceIntegralMap p u n :=
  SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.source p u n

theorem target : (F).map (HomologicalComplex.homologyMap
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.targetRefinement p u n) 1) ≫
      (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.targetIso p u n).hom =
    (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X₂ n).hom ≫
      SectionRefinementData.IntrinsicPadicGeometricSectionRefinementData.targetIntegralMap p u n :=
  SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.target p u n

theorem naturality : (F).map (HomologicalComplex.homologyMap
    (QuotientCoordinates.IntrinsicPadicGeometricQuotientCoordinates.geometricMap p u n) 1) ≫
      (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.sourceIso p u n).hom =
    (SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.targetIso p u n).hom ≫
      CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceHOneMap p u n :=
  SmallCoefficientOne.IntrinsicPadicGeometricSmallCoefficientHOne.naturality p u n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallAssemblyOne.IntrinsicPadicGeometricSmallAssemblyHOne
