import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IntegerTwistSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.DegreeRank
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NegativeLaurentSections

/-! # Twist Section Rank -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistSectionRank

noncomputable section

/-! Exact section ranks of nonnegative twists and vanishing of
negative twists on positive-dimensional projective space over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem specFieldSectionRing_isField : IsField Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)

theorem projectiveTwistSections_finrank (j : Fin (n + 1)) (d : ℕ) :
    letI := Module.compHom Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j d, ⊤)
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
    Module.finrank Γ(Spec (.of K), ⊤) Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j d, ⊤) =
      (d + n).choose n := by
  let := (specFieldSectionRing_isField K).toField
  let := Module.compHom Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j (d : ℤ), ⊤)
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (n + 1))).appTop.hom
  let e := (IntegerTwistSections.integerTwistGlobalSectionsLaurentEquiv (R := K) j (d : ℤ)).trans
    (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.laurentZeroCyclesEquivPolynomials K j d)
  exact e.finrank_eq.trans
    (Homogeneous.DegreeRank.GradedHilbert.homogeneousDegree_finrank Γ(Spec (.of K), ⊤) n d)

theorem projectiveTwistSections_subsingleton_of_neg (hn : 0 < n) (j : Fin (n + 1)) (d : ℤ) (hd : d < 0) :
    Subsingleton Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) j d, ⊤) := by
  let : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let := NegativeLaurentSections.negativeLaurentZeroCycles_subsingleton (R := K) (σ := Fin (n + 1)) d hd
  exact (IntegerTwistSections.integerTwistGlobalSectionsLaurentEquiv (R := K) j d).injective.subsingleton

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistSectionRank
