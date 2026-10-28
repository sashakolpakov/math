import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FrameEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.MapRestriction

/-! # Twist Frame Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistFrameAction

noncomputable section

/-! A native map of integer twists acts in its Čech frame by the
restriction of its coefficient on the first chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

def frame (i j : σ) (d : ℤ) :=
  AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j d)

theorem factor_frame (j : σ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → ULift.{u} σ)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d, AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a)) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a j d).hom x =
      (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a)
        (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization _ _ _
          (frame (R := R) (a 0).down j d)
          (Over.mk (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0))))).symm x :=
  FrameEvaluation.restriction_apply (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) (a 0).down j d) x

theorem factor_action (j : σ) (d e : ℤ) {n : ℕ} (a : Fin (n + 1) → ULift.{u} σ)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶ AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j e)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d, AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a)) :
    (show Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a) from
      (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a j e).hom
        (f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a) x)) =
      (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
        (AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a 0).down)
          (frame (R := R) (a 0).down j d) (frame (R := R) (a 0).down j e) f) *
      (show Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a) from
        (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a j d).hom x) := by
  rw [factor_frame, factor_frame]
  exact Frame.MapRestriction.coordinate_on_subopen (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a 0).down)
    (frame (R := R) (a 0).down j d) (frame (R := R) (a 0).down j e) f
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistFrameAction
