import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Degree Rank -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeRank.GradedHilbert

noncomputable section

/-! The actual homogeneous degree-d polynomial space on projective
n-space has binomial(d+n,n) dimensions over a field. -/

universe u

theorem homogeneousDegree_finrank (K : Type u) [Field K] (n d : ℕ) :
    Module.finrank K (Hilbert.Polynomial.GradedHilbert.grading K n d) = (d + n).choose n := by
  let := Fintype.ofFinite (CoordinateBasis.GradedHilbert.DegreeMonomials n d)
  rw [Module.finrank_eq_card_basis (CoordinateBasis.GradedHilbert.degreeMonomialBasis K n d), ← Nat.card_eq_fintype_card]
  exact Hilbert.Existence.GradedHilbert.card_degreeExponents n d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeRank.GradedHilbert
