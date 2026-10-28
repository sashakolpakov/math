import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.AnalyticConeCoordinates

/-! # Cone Unit -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ConeUnit.Dolbeault

noncomputable section

section

/-! The original projective twist analytification unit evaluates its original algebraic frame coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistOpenSectionFunction_unit (n : ℕ) (U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (j : Fin (n + 1)) (d : ℤ)
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.obj (op U))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U) :
    Projective.TransitionEvaluation.Dolbeault.projectiveTwistOpenSectionFunction n U i hi j d
        ((Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app (op U) m) p =
      Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U
        ((FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n U i hi j d).hom.val.app (op (Over.mk (𝟙 U))) m) p := by
  have h := Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit_frame (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)
      (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n U i hi j d) m
  exact congrArg (fun f : (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj.obj
    (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U)) => (ContMDiffMap.evalRingHom p) f) h

def projectiveAlgebraicTwistIntersectionCoefficient (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.obj
      (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) : Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) :=
  (FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame n (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) i
    (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d).hom.val.app
      (op (Over.mk (𝟙 (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)))) m

theorem projectiveTwistIntersectionFunction_unit (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.obj
      (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) :
    IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n s i hi j d
        ((Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) m) p =
      Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)
        (projectiveAlgebraicTwistIntersectionCoefficient n s i hi j d m) p :=
  projectiveTwistOpenSectionFunction_unit n (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) i
    (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) j d m p

end

/-! The actual algebraic twist section unit has the expected homogeneous-cone evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistAnalyticConeCoordinates_unit (n : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (m : (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.obj
      (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (Projective.AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n s i hi j d
      ((Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d)).app (op (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s)) m)).val.val x =
      x.val i ^ d * Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n s) (projectiveAlgebraicTwistIntersectionCoefficient n s i hi j d m)
          (Projective.AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n s hs x) :=
  (Projective.AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates_evaluate n s hs i hi j d _ x).trans
    (congrArg (x.val i ^ d * ·)
      (projectiveTwistIntersectionFunction_unit n s i hi j d m (Projective.AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n s hs x)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ConeUnit.Dolbeault
