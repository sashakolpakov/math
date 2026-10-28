import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceTopRefinement

/-! # Point Value Edges -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The two bounded point values are the original common/ordinary
crystalline edges, with the same explicit top-degree sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq) (n : ℕ)

theorem Geometry.AbelianH1Model.truncatedOrdinaryPointValue_eq (hpos : 0 < A.dimension) :
    A.truncatedOrdinaryPointValue n =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        A.truncatedCrystallineTopEdge n (A.truncatedSmallPointClass n hpos) := by
  have h := IntegralComparison.TruncatedModel.TopCoverPositiveValue.bounded_value q (ZMod q) n
    (A.truncatedModel n).scheme A.specialFiber.scheme (A.truncatedReduction n)
    (A.truncatedReductionSquare n) (A.truncatedPointValueResolution n) A.dimension hpos
    (A.truncatedTraceCover n) (A.truncatedTraceCover_top n) (A.truncatedTraceCover_affine n)
    (A.truncatedTracePointClass n)
  rw [A.truncatedOrdinaryPointValue_coordinates n hpos] at h
  exact h

variable (m : ℕ) (hm : ¬q ∣ m)

theorem Geometry.AbelianH1Model.truncatedFinitePointValue_eq (hpos : 0 < A.dimension) :
    A.truncatedFinitePointValue n m hm =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        A.truncatedShiftCommonEdge n m hm (A.truncatedShiftPointClass n m hm hpos) := by
  have h := IntegralComparison.TruncatedModel.TopCoverPositiveValue.bounded_value q (ZMod q) n
    (A.truncatedShiftModel n m hm) A.specialFiber.scheme (A.truncatedShiftReduction n m hm)
    (A.truncatedShiftModel_square n m hm) (A.truncatedPointValueResolution n) A.dimension hpos
    (A.truncatedFinitePointCover n m hm) (A.truncatedFinitePointCover_top n m hm)
    (A.truncatedFinitePointCover_affine n m hm) (A.truncatedFiniteTracePointClass n m hm)
  have hc := IntegralComparison.TruncatedModel.MorphismSourceTopRefinement.comparison q (ZMod q) n
    (A.truncatedShiftOver n m hm) A.dimension (A.truncatedShiftReduction n m hm)
    (A.truncatedShiftModel_square n m hm) (A.truncatedPointValueResolution n)
    (A.truncatedFiniteSmallPointClass n m hm hpos)
  rw [A.truncatedFiniteSmallPointClass_common n m hm hpos] at hc
  exact h.trans (congrArg
    (fun x => ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension • x) hc.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
