import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReductionCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DeRhamReduction

/-! # Small Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReduction.IntrinsicPadicGeometricSmallReduction

noncomputable section

/-! Actual geometric pullback and source-cover refinement agree
on the original reduced native integral de Rham classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂) (n : ℕ)

theorem source (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₁ 1) :
    (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.iso p u n).hom
      (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n
        (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₁ n x)) =
          DeRhamReduction.IntrinsicPadicGeometricDeRhamReduction.commonReduction p u n x := by
  have h := ConcreteCategory.congr_hom (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.source p u n)
    (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₁ n x)
  exact h.trans ((congrArg (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.sourceMap p u n)
    (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.coordinates p X₁ n x)).trans
      (DeRhamReduction.IntrinsicPadicGeometricDeRhamReduction.source p u n x))

theorem target (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₂ 1) :
    (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.iso p u n).hom
      (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n
        (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n
          (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₂ n x))) =
            DeRhamReduction.IntrinsicPadicGeometricDeRhamReduction.commonReduction p u n (DeRham.Int.pullback u 1 x) := by
  have h := ConcreteCategory.congr_hom (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.target p u n)
    (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₂ n x)
  exact h.trans ((congrArg (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.targetMap p u n)
    (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.coordinates p X₂ n x)).trans
      (DeRhamReduction.IntrinsicPadicGeometricDeRhamReduction.target p u n x))

theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₂ 1) :
    QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n
      (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n
        (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₂ n x)) =
    QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n
      (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₁ n (DeRham.Int.pullback u 1 x)) := by
  apply (QuotientOneCoordinates.IntrinsicPadicGeometricThreeTermCoordinates.iso p u n).toLinearEquiv.injective
  exact (target p u n x).trans (source p u n (DeRham.Int.pullback u 1 x)).symm

theorem linearMap : (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n).hom.comp
    ((QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n).hom.comp
      (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₂ n)) =
    (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n).hom.comp
      ((SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X₁ n).comp (DeRham.Int.pullback u 1)) := by
  apply LinearMap.ext
  intro x
  exact naturality p u n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReduction.IntrinsicPadicGeometricSmallReduction
