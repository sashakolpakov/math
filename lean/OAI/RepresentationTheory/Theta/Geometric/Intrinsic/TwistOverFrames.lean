import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistFrames
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions

/-! # Twist Over Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistOverFrames

noncomputable section

/-! Native hyperplane pullback frames on the over-site, including arbitrary
subopens of their overlaps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (d : ℤ)

def algebraicPullbackTwistOverFrame (i : Fin (n + 1)) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf).over
      (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i) ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)) :=
  AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _ (TwistFrames.algebraicPullbackTwistFrame f d i)

def algebraicPullbackTwistOverFrameOn (i : Fin (n + 1)) (W : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf).over W ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over W) :=
  AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf _ _
    (algebraicPullbackTwistOverFrame f d i) (Over.mk (homOfLE hW))

theorem algebraicPullbackTwistOverFrame_transition (i k : Fin (n + 1)) :
    (algebraicPullbackTwistOverFrameOn f d i
      (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k))).hom =
    (algebraicPullbackTwistOverFrameOn f d k
      (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
      (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf
        (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
        ((PowerGauge.projectivePullbackTransitionUnit f i k ^ d :
          Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)ˣ) :
          Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) := by
  have h := AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf
    (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) _ _
    ((PowerGauge.projectivePullbackTransitionUnit f i k ^ d :
      Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)ˣ) :
      Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k))
    (TwistFrames.algebraicPullbackTwistFrame_transition f d i k)
  rw [AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization,
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] at h
  exact h

theorem algebraicPullbackTwistOverFrameOn_transition (i k : Fin (n + 1)) (W : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    (algebraicPullbackTwistOverFrameOn f d i W
      (hW.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)))).hom =
    (algebraicPullbackTwistOverFrameOn f d k W
      (hW.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k)))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W
        (PowerGaugeCover.restrictRegularUnit hW (PowerGauge.projectivePullbackTransitionUnit f i k ^ d) : Γ(X, W)) := by
  have h := AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions.restrictOverTrivialization_hom_eq_comp_scalar
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf hW _ _ _
    (algebraicPullbackTwistOverFrame_transition f d i k)
  dsimp only [algebraicPullbackTwistOverFrameOn] at h
  rw [AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.restrictOverTrivialization_comp, AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.restrictOverTrivialization_comp] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistOverFrames
