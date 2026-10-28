import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FrameScalars
import OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameScalarTransport
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SectionCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions

/-! # Frame Transitions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameTransitions.Dolbeault

noncomputable section

/-! The actual analytified projective twists have the original integer-power
transition functions on coordinate overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistTransitionSection (n : ℕ) (i k : Fin (n + 1)) (d : ℤ) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :=
  ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k) ^ d :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)ˣ)

theorem projectiveTwistTransitionSection_top (n : ℕ) (i k : Fin (n + 1)) (d : ℤ) :
    ((SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := ℂ) i k ^ d :
      Γ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)ˣ) :
        Γ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)) =
      SheafCohomology.Projective.OpenFrames.Scheme.Modules.openTopSection (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        (projectiveTwistTransitionSection n i k d) := by
  unfold SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit projectiveTwistTransitionSection
  rw [← map_zpow]
  rfl

def projectiveAlgebraicTwistOpenFrame (n : ℕ) (U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (j : Fin (n + 1)) (d : ℤ) :
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).over U ≅
      SheafOfModules.unit ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf.over U) :=
  SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hi
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := ℂ) i j d))

def projectiveAnalytifiedTwistOpenFrame (n : ℕ) (U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (i : Fin (n + 1)) (hi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).over (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U) ≅
      SheafOfModules.unit ((Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).over
        (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U)) :=
  Analytification.OpenTrivialization.holomorphicAnalytificationOpenUnitIso (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) U _
    (projectiveAlgebraicTwistOpenFrame n U i hi j d)

theorem projectiveAlgebraicTwistOpenFrame_transition (n : ℕ)
    (i k j : Fin (n + 1)) (d : ℤ) :
    (projectiveAlgebraicTwistOpenFrame n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      i (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k) j d).hom =
    (projectiveAlgebraicTwistOpenFrame n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      k (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k) j d).hom ≫
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) (projectiveTwistTransitionSection n i k d) := by
  apply Open.FrameScalarTransport.algebraicOverFrame_scalar
  rw [← projectiveTwistTransitionSection_top]
  exact SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial.coordinateHyperplaneTwistTrivialization_restrict_transition i k j d

theorem projectiveAnalytifiedTwistOpenFrame_transition (n : ℕ)
    (i k j : Fin (n + 1)) (d : ℤ) :
    (projectiveAnalytifiedTwistOpenFrame n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      i (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k) j d).hom =
    (projectiveAnalytifiedTwistOpenFrame n (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      k (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k) j d).hom ≫
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
        (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k))
        (Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
          (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) (projectiveTwistTransitionSection n i k d)) :=
  Holomorphic.FrameScalars.holomorphicAnalytificationOpenUnitIso_scalar (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) _ _ _ _ _
    (projectiveAlgebraicTwistOpenFrame_transition n i k j d)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.FrameTransitions.Dolbeault
