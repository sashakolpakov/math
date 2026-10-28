import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackFrames
import OAI.RepresentationTheory.Theta.Geometric.OpenFrameScalars
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.Open

/-! # Frame Ratios -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FrameRatios

noncomputable section

/-! Express native hyperplane-frame transitions by Presentations's actual coordinate
ratios. These formulas retain arbitrary base schemes and their nilpotents. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem e34_coordinateRatio_section {R : Type u} [CommRing R] {n : ℕ} (i k : Fin (n + 1)) :
    Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X k)) =
      SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k := by
  rw [HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize_X, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  apply congrArg (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
  simp only [HilbertScheme.Presentations.Projective.IdealRecovery.GradedHilbert.coordinateFraction, HomogeneousLocalization.Away.isLocalizationElem, pow_one]

theorem morphismRestrict_topSection {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens)
    (r : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv r) = (f ⁻¹ᵁ U).topIso.inv (f.app U r) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  simp only [Scheme.Hom.resLE_app_top, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply, Scheme.Hom.appLE_eq_app]

variable {R : Type} [CommRing R] {n : ℕ} {X : Scheme}
  (a : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem hyperplanePullback_overlap_ratio (i k : Fin (n + 1)) :
    let W := SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
    (a ∣_ W).appTop (W.topIso.inv (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k)) =
      (a ⁻¹ᵁ W).topIso.inv
        (a.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (a ⁻¹ᵁ W)
          (a.preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k))
          (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)) := by
  dsimp only
  rw [morphismRestrict_topSection]
  apply congrArg ((a ⁻¹ᵁ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv)
  change a.app (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
    ((Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map
      (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)) = _
  rw [Scheme.Hom.app_eq_appLE]
  exact ConcreteCategory.congr_hom
    (a.map_appLE le_rfl (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op)
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)

theorem hyperplanePullbackFrame_transition_on (j i k : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ a ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hk : U ≤ a ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hi (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame a j i)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hk (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame a j k)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv
          (a.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) U hi (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k))) := by
  let W := SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
  have hU : U ≤ a ⁻¹ᵁ W := by
    dsimp only [W]
    rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf hi hk
  have h := HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame_transition a j i k
  rw [hyperplanePullback_overlap_ratio] at h
  have hr := RepresentationTheory.Theta.Geometric.OpenFrameScalars.restrictOpenFrame_scalar _ hU _ _
    (a.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (a ⁻¹ᵁ W)
      (a.preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k))
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)) h
  rw [SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp,
    SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp] at hr
  have hs := ConcreteCategory.congr_hom
    (a.appLE_map (a.preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)) (homOfLE hU).op)
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)
  change X.presheaf.map (homOfLE hU).op
      (a.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (a ⁻¹ᵁ W) _
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)) =
    a.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) U hi (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) at hs
  rw [hs] at hr
  exact hr

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FrameRatios
