import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors

/-! # Frame Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.FrameCoefficients.Dolbeault

noncomputable section

/-! The actual algebraic open-frame coefficients are the original base-Cech trivialization coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAlgebraicTwistOpenCoefficient (n : ℕ) (U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (j : Fin (n + 1)) (d : ℤ)
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.obj (op U)) : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, U) :=
  (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n U i hi j d).hom.val.app (op (Over.mk (𝟙 U))) m

theorem projectiveAlgebraicTwistOpenCoefficient_restrict (n : ℕ)
    {U V : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens} (hVU : V ≤ U)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (j : Fin (n + 1)) (d : ℤ)
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.obj (op U)) :
    projectiveAlgebraicTwistOpenCoefficient n V i (hVU.trans hi) j d
      ((SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.map (homOfLE hVU).op m) =
      (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map (homOfLE hVU).op
        (projectiveAlgebraicTwistOpenCoefficient n U i hi j d m) := by
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d
  let R := (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
  let e := ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n U i hi j d
  have h := ConcreteCategory.congr_hom
    (SheafCohomology.Projective.TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso_naturality
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1))) M hVU e) m
  have he := congrArg (fun eV : M.over V ≅ SheafOfModules.unit (R.over V) =>
    eV.hom.val.app (op (Over.mk (𝟙 V))) (M.val.map (homOfLE hVU).op m))
      (ProjectiveTwist.FrameRestriction.Dolbeault.projectiveAlgebraicTwistOpenFrame_restrict n hVU i hi j d)
  exact he.symm.trans h

theorem projectiveTwistBaseFactor_coefficient (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (a : Fin (q + 1) → ULift.{0} (Fin (n + 1)))
    (m : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ)) q a) :
    (SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := ℂ) a j d).hom m =
      projectiveAlgebraicTwistOpenCoefficient n (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := ℂ) a)
        (a 0).down (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := ℂ) a 0) j d m := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.FrameCoefficients.Dolbeault
