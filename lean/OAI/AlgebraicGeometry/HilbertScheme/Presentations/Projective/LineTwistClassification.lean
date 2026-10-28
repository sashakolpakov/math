import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatchingFrameSystems
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistTransitionValue
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.IntrinsicFrames

/-! # Line Twist Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTwistClassification

noncomputable section

/-! Every actual line bundle on projective space over a field is
isomorphic to an integer twist, obtained by gluing its normalized frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

theorem projectiveLineBundle_is_twist :
    Nonempty (L.sheaf ≅ SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (-LineCommonExponent.projectiveLineCommonExponent K L)) := by
  apply MatchingFrameSystems.exists_moduleIso_of_matching_frame_transitions L.sheaf
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (-LineCommonExponent.projectiveLineCommonExponent K L))
    (fun i : Fin (n + 1) => Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i))
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := K))
    (OverlapSectionUnits.projectiveDoubleOpen K)
    (fun i j => (OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left)
    (fun i j => (OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right)
    (fun i j => (OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).ge)
    (Normalized.IntrinsicFrames.projectiveNormalizedNativeFrame K L)
    (fun i => SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := K) i 0 (-LineCommonExponent.projectiveLineCommonExponent K L))
  intro i j
  apply (ConcreteCategory.bijective_of_isIso (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom).injective
  rw [Normalized.IntrinsicFrames.projectiveNormalizedNativeFrame_transition, TwistTransitionValue.projectiveTwistFrame_transition, neg_neg]

def projectiveLineBundleTwistIso :
    L.sheaf ≅ SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) (-LineCommonExponent.projectiveLineCommonExponent K L) :=
  (projectiveLineBundle_is_twist K L).some

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTwistClassification
