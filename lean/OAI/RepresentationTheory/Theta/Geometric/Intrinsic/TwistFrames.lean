import OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction
import OAI.RepresentationTheory.Theta.Geometric.Pullback.TwistTransitions

/-! # Twist Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistFrames

noncomputable section

/-! Native chart frames of the actual hyperplane pullback, with their
transition law on the actual inverse-image overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (d : ℤ)

def algebraicPullbackTwistFrame (i : Fin (n + 1)) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf).restrict
      (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i).toScheme :=
  Pullback.Algebraic.pullbackOpenFrame f (AlgebraicQuotient.algebraicTwistBundle n d).sheaf (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)
    (Pullback.Algebraic.algebraicTwistRestrictionFrame n d i)

set_option backward.isDefEq.respectTransparency false in
theorem algebraicPullbackTwistFrame_transition (i k : Fin (n + 1)) :
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k))
      (algebraicPullbackTwistFrame f d i)).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k))
      (algebraicPullbackTwistFrame f d k)).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((Units.map (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).topIso.inv.hom.toMonoidHom
          (PowerGauge.projectivePullbackTransitionUnit f i k ^ d) :
            Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)ˣ) :
            Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)) := by
  have hl := congrArg Iso.hom (Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f (AlgebraicQuotient.algebraicTwistBundle n d).sheaf
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k) (Pullback.Algebraic.algebraicTwistRestrictionFrame n d i))
  have hr := congrArg Iso.hom (Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict f (AlgebraicQuotient.algebraicTwistBundle n d).sheaf
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k) (Pullback.Algebraic.algebraicTwistRestrictionFrame n d k))
  exact hl.trans ((Pullback.TwistTransitions.pullbackTwistOverlapFrame_transition f d i k).trans
    (congrArg (fun t => t ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
      ((Units.map (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).topIso.inv.hom.toMonoidHom
        (PowerGauge.projectivePullbackTransitionUnit f i k ^ d) :
          Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)ˣ) :
          Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤))) hr.symm))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TwistFrames
