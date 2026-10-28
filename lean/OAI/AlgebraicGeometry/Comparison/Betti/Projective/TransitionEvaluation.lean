import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CoordinateEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameTransitions

/-! # Transition Evaluation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation

/-! The original holomorphic evaluation of every integer-twist transition is
the corresponding integer power of the actual projective coordinate ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

section

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem regularHolomorphicSectionMap_unit_zpow (U : X.left.Opens) (u : Γ(X.left, U)ˣ)
    (d : ℤ) (p : Open.AffineIsoEvaluation.analyticOpen X U) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap X U ((u ^ d : Γ(X.left, U)ˣ) : Γ(X.left, U)) p =
      (Holomorphic.RegularSections.regularHolomorphicSectionMap X U (u : Γ(X.left, U)) p) ^ d := by
  let f : Γ(X.left, U) →+* ℂ :=
    (ContMDiffMap.evalRingHom p).comp (Holomorphic.RegularSections.regularHolomorphicSectionMap X U).toRingHom
  exact (f.toMonoidHom.comp (Units.coeHom Γ(X.left, U))).map_zpow u d

end

namespace Dolbeault

open OAI.AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveLocalEquation_evaluation_all (n : ℕ) (i k : Fin (n + 1))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k) p =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
  by_cases hki : k = i
  · subst k
    have hp : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
      apply (Intersections.Dolbeault.mem_projectiveStandardCover n i p.val).mp
      rw [Intersections.Dolbeault.projectiveStandardCover_eq_analyticOpen]
      exact p.property
    rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self, map_one]
    exact hp.symm
  · exact CoordinateEvaluation.Dolbeault.projectiveLocalEquation_evaluation n i ⟨k, hki⟩ p

theorem projectiveTransitionUnit_evaluation (n : ℕ) (i k : Fin (n + 1))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k) :
          Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) p =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val) := by
  change Open.AffineIsoEvaluation.sectionEvaluationOn (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map
      (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)).op
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k)) p = _
  exact (Open.AffineIsoEvaluation.sectionEvaluationOn_restrict (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k) p).trans
      (projectiveLocalEquation_evaluation_all n i k _)

theorem projectiveTwistTransitionSection_evaluation (n : ℕ) (i k : Fin (n + 1)) (d : ℤ)
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) :
    Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d) p =
      (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) ^ d := by
  rw [ProjectiveTwist.FrameTransitions.Dolbeault.projectiveTwistTransitionSection, regularHolomorphicSectionMap_unit_zpow,
    projectiveTransitionUnit_evaluation]

end Dolbeault

end AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation

namespace AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation.Dolbeault

/-! Actual twist sections in the two native overlap frames satisfy the
coordinate-ratio transition formula, with the original analytification map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistOpenSectionFunction (n : ℕ) (U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U))) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
      (M := Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U) :=
  Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _ (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAnalytifiedTwistOpenFrame n U i hi j d) a

theorem projectiveTwistOpenSectionFunction_transition (n : ℕ) (i k j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op
      (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k))))
    (p : Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) :
    projectiveTwistOpenSectionFunction n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        i (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k) j d a p =
      projectiveTwistOpenSectionFunction n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        k (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k) j d a p *
        (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm p.val)) ^ d := by
  have h := Holomorphic.FrameScalars.holomorphicAnalytificationFrameSection_scalar (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) _ _ _
    (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveAlgebraicTwistOpenFrame_transition n i k j d) a
  have hp := congrArg (fun f : (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf
      (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj.obj (op
      (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k))) =>
        (ContMDiffMap.evalRingHom p) f) h
  change projectiveTwistOpenSectionFunction n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      i (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k) j d a p =
    projectiveTwistOpenSectionFunction n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      k (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k) j d a p *
      Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        (ProjectiveTwist.FrameTransitions.Dolbeault.projectiveTwistTransitionSection n i k d) p at hp
  rw [projectiveTwistTransitionSection_evaluation] at hp
  exact hp

end AlgebraicGeometry.Comparison.Betti.Projective.TransitionEvaluation.Dolbeault

end

end OAI
