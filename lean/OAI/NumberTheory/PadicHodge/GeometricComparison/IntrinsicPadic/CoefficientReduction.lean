import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReduction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient

/-! # Coefficient Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction

noncomputable section

/-! The actual small quotient reduction square after the native
coefficient functor and descent to p-adic scalars. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p

def sourceMap := (D).map ((F).map (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n))
def targetMap := (D).map ((F).map (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n))
def geometricMap := (D).map ((F).map (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n))

def reduction (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :=
  Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1)
    (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X n x)

theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₂ 1) :
    geometricMap p u n (targetMap p u n (reduction p n X₂ x)) =
      sourceMap p u n (reduction p n X₁ (DeRham.Int.pullback u 1 x)) := by
  let y := SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₂ n x
  have h₁ := congrArg (geometricMap p u n)
    (Coefficient.IntrinsicPadicCoefficientDescent.natural p (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n) y).symm
  have h₂ := (Coefficient.IntrinsicPadicCoefficientDescent.natural p (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n)
    (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n y)).symm
  have h₃ := congrArg (Coefficient.IntrinsicPadicCoefficientDescent.equiv p _)
    (SmallReduction.IntrinsicPadicGeometricSmallReduction.naturality p u n x)
  have h₄ := Coefficient.IntrinsicPadicCoefficientDescent.natural p (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n)
    (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₁ n (DeRham.Int.pullback u 1 x))
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction
