import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionRank
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistLineBundles

/-! # Hyperplane Rigidity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.HyperplaneRigidity

noncomputable section

/-! In positive projective dimension, a line bundle with n+1 global
sections is O(1). Every base-preserving projective automorphism preserves O(1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem projectiveLineBundle_is_nat_twist_of_rank (hn : 0 < n)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) (m : ℕ)
    (hL : SectionRank.projectiveSectionRank K L.sheaf = (m + n).choose n) :
    Nonempty (L.sheaf ≅ SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (m : ℤ)) := by
  let e := LineTwistClassification.projectiveLineBundleTwistIso K L
  have hr := (SectionRank.projectiveSectionRank_iso K e).symm.trans hL
  have hd := SectionRank.projectiveSectionRank_twist_eq_natDegree K hn 0 (-LineCommonExponent.projectiveLineCommonExponent K L) m hr
  exact ⟨e ≪≫ eqToIso (congrArg (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1))) hd)⟩

theorem projectiveAutomorphism_preserves_nat_twist (hn : 0 < n)
    (e : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ≅ Proj (Hilbert.Polynomial.GradedHilbert.grading K n))
    (he : e.hom ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (m : ℤ)) ≅
        SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (m : ℤ)) := by
  apply projectiveLineBundle_is_nat_twist_of_rank K hn
    ((TwistLineBundles.projectiveTwistLineBundle K n (m : ℤ)).pullback e.hom) m
  change SectionRank.projectiveSectionRank K ((Scheme.Modules.pullback e.hom).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (m : ℤ))) = (m + n).choose n
  rw [SectionRank.projectiveSectionRank_pullback K e he, SectionRank.projectiveSectionRank_twist_nat]

theorem projectiveLineBundle_is_one_twist_of_rank (hn : 0 < n)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))
    (hL : SectionRank.projectiveSectionRank K L.sheaf = n + 1) :
    Nonempty (L.sheaf ≅ SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) 1) := by
  let e := LineTwistClassification.projectiveLineBundleTwistIso K L
  have hr := (SectionRank.projectiveSectionRank_iso K e).symm.trans hL
  have hd := SectionRank.projectiveSectionRank_twist_eq_dimension K hn 0 (-LineCommonExponent.projectiveLineCommonExponent K L) hr
  exact ⟨e ≪≫ eqToIso (congrArg (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1))) hd)⟩

theorem projectiveAutomorphism_preserves_one_twist (hn : 0 < n)
    (e : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ≅ Proj (Hilbert.Polynomial.GradedHilbert.grading K n))
    (he : e.hom ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) 1) ≅
        SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) 1) := by
  apply projectiveLineBundle_is_one_twist_of_rank K hn ((TwistLineBundles.projectiveTwistLineBundle K n 1).pullback e.hom)
  change SectionRank.projectiveSectionRank K ((Scheme.Modules.pullback e.hom).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) 1)) = n + 1
  rw [SectionRank.projectiveSectionRank_pullback K e he]
  simpa only [Int.natCast_one, Nat.add_comm 1 n, Nat.choose_succ_self_right] using
    SectionRank.projectiveSectionRank_twist_nat K (n := n) 0 1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.HyperplaneRigidity
