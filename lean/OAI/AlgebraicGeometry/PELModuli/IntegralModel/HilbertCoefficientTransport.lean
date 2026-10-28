import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Hilbert Coefficient Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertCoefficientTransport

noncomputable section

/-! Presentations's actual homogeneous coordinate Hilbert polynomial is preserved
under coefficient-field extension, using the degree-quotient base-change
isomorphisms. In particular this covers the canonical Γ(Spec K) comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert
universe u v
variable {K : Type u} [Field K] {L : Type v} [Field L] {n : ℕ}
  (φ : K →+* L) (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n))

theorem hilbertFunction_coefficient_map (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal d = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let := φ.toAlgebra
  change Module.finrank L (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := L) I).toIdeal d) =
    Module.finrank K (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
  exact (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := L) I d).finrank_eq.symm.trans
    (Module.finrank_baseChange (R := L) (S := K) (M' := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d))

theorem hasHilbertPolynomial_coefficient_map_iff (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  unfold HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  simp only [hilbertFunction_coefficient_map]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertCoefficientTransport
