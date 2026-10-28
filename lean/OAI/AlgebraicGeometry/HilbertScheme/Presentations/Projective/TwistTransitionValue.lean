import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectiveRatio
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.UnitSectionTransport
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions

/-! # Twist Transition Value -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistTransitionValue

noncomputable section

/-! The native twist O(d) has Presentations scalar transition exponent -d.
This is an equality of actual overlap sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem projectiveTwistFrame_transition (d : ℤ) (i j : Fin (n + 1)) :
    (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
      (FrameTransitionCocycles.frameTransitionValue
        (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left)
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := K) i 0 d))
        (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right)
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := K) j 0 d))) =
      ((OverlapRatioUnits.projectiveOverlapRatioUnit K i j ^ (-d) :
        Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
          Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)) := by
  have h := Intrinsic.FrameScalars.frameTransitionValue_of_native_transition
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i j)
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := K) i 0 d))
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i j)
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := K) j 0 d))
    (SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := K) i j ^ d)
    (SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial.coordinateHyperplaneTwistTrivialization_restrict_transition (R := K) i j 0 d)
  have ht := congrArg (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom h
  have hu := UnitSectionTransport.sectionIso_unit_inverse_power (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i j).topIso
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := K) i j) d
  have h' := ht.trans hu
  simpa only [Intrinsic.ProjectiveRatio.projectiveOverlapRatioUnit_eq_native] using! h'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistTransitionValue
