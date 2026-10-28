import OAI.RepresentationTheory.Theta.Geometric.ProductFrames
import OAI.RepresentationTheory.Theta.Geometric.PowerOpenFrameRestriction

/-! # Quotient Power Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientPowerFrames

noncomputable section

/-! Native frames and transition functions for each actual tensor power of
the consecutive theta quotient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n m : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)

def thetaQuotientPowerFrameOn (i : Fin (n + 1)) (j : Fin (m + 1)) (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)
    (hg : W ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j) (k : ℕ) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf k).restrict W.ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj W.toScheme :=
  AlgebraicPowerFrames.tensorPowerOpenFrame _ W (ProductFrames.thetaQuotientFrameOn f g i j W hf hg) k

theorem thetaQuotientPowerFrameOn_restrict (i : Fin (n + 1)) (j : Fin (m + 1))
    {U V : X.Opens} (h : V ≤ U)
    (hf : U ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)
    (hg : U ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j) (k : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (thetaQuotientPowerFrameOn f g i j U hf hg k) =
      thetaQuotientPowerFrameOn f g i j V (h.trans hf) (h.trans hg) k := by
  unfold thetaQuotientPowerFrameOn
  rw [PowerOpenFrameRestriction.tensorPowerOpenFrame_restrict, ProductFrames.thetaQuotientFrameOn_restrict]

theorem thetaQuotientPowerFrameOn_transition (i i' : Fin (n + 1)) (j j' : Fin (m + 1))
    (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i i')
    (hg : W ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) j j') (k : ℕ) :
    (thetaQuotientPowerFrameOn f g i j W
      (hf.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i i')))
      (hg.trans (g.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) j j'))) k).hom =
    (thetaQuotientPowerFrameOn f g i' j' W
      (hf.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i i')))
      (hg.trans (g.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) j j'))) k).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (W.topIso.inv
        (((PowerGaugeCover.restrictRegularUnit hg (PowerGauge.projectivePullbackTransitionUnit g j j') *
          (PowerGaugeCover.restrictRegularUnit hf (PowerGauge.projectivePullbackTransitionUnit f i i'))⁻¹) ^ k : Γ(X, W)ˣ) : Γ(X, W))) := by
  have h := AlgebraicPowerFrames.tensorPowerOpenFrame_scalar (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf W _ _ _
    (ProductFrames.thetaQuotientFrameOn_transition f g i i' j j' W hf hg) k
  apply h.trans
  congr 2
  exact (map_pow W.topIso.inv.hom _ k).symm

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientPowerFrames
