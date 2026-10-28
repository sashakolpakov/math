import OAI.AlgebraicGeometry.Comparison.Betti.NestedOpenFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FrameGeneratorRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation

/-! # Frame Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameRestriction.Dolbeault

noncomputable section

/-! The chosen projective twist frames commute with original restriction maps
between arbitrary algebraic opens inside the same standard coordinate chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAlgebraicTwistOpenFrame_restrict (n : ℕ)
    {U V : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens} (hVU : V ≤ U)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (j : Fin (n + 1)) (d : ℤ) :
    SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) U
        (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n U i hi j d) (Over.mk (homOfLE hVU)) =
      FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n V i (hVU.trans hi) j d := by
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d
  let e := SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i j d)
  have hu := SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hi
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i j d)
  have hv := SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization (hVU.trans hi)
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i j d)
  exact (congrArg (fun f => SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf M U f (Over.mk (homOfLE hVU))) hu).trans
      ((NestedOpenFrames.Dolbeault.restrictOpenFrame_trans (Z := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
        (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf M hi hVU e).trans hv.symm)

theorem projectiveTwistOpenSectionFunction_restrict (n : ℕ)
    {U V : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens} (hVU : V ≤ U)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U)))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) V) :
    Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n V i (hVU.trans hi) j d
        ((Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map
          (homOfLE (Open.SmoothForms.analyticOpen_mono (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) hVU)).op a) p =
      Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n U i hi j d a
        ⟨p.val, Open.SmoothForms.analyticOpen_mono (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) hVU p.property⟩ := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d
  have h := Holomorphic.FrameGeneratorRestriction.holomorphicAnalytificationOpenUnitIso_section_restrict X hVU M
    (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n U i hi j d) a
  have he := projectiveAlgebraicTwistOpenFrame_restrict n hVU i hi j d
  have hc := congrArg (fun eV => Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _
      (Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso X V M eV)
      ((Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono X hVU)).op a)) he
  exact congrArg (fun f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel X) (M := Open.AffineIsoEvaluation.analyticOpen X V) =>
    f.val p) (hc.symm.trans h)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameRestriction.Dolbeault
