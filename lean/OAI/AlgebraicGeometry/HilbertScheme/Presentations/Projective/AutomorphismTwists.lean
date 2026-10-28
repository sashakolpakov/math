import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.HyperplaneRigidity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroLineBundles

/-! # Automorphism Twists -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AutomorphismTwists

noncomputable section

/-! Every base-preserving automorphism of projective space over a
field preserves all native nonnegative twists, in every dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem projectiveAutomorphism_preserves_native_twists
    (e : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ≅ Proj (Hilbert.Polynomial.GradedHilbert.grading K n))
    (he : e.hom ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) (0 : Fin (n + 1)) m) ≅
        SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) (0 : Fin (n + 1)) m) := by
  by_cases hn : 0 < n
  · exact HyperplaneRigidity.projectiveAutomorphism_preserves_nat_twist K hn e he m
  · have hn0 : n = 0 := by omega
    subst n
    exact ZeroLineBundles.projectiveZeroLineBundles_iso K ((TwistLineBundles.projectiveTwistLineBundle K 0 (m : ℤ)).pullback e.hom)
      (TwistLineBundles.projectiveTwistLineBundle K 0 (m : ℤ))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AutomorphismTwists
