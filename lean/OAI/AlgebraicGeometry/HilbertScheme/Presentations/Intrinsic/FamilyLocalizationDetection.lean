import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatCoefficientCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealLocalizationDetection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction
import Mathlib.RingTheory.Flat.Localization

/-! # Family Localization Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FamilyLocalizationDetection.GradedHilbert

noncomputable section

/-! Native projective families over arbitrary affine rings are detected
by their actual pullbacks to all maximal local coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {n : ℕ}

theorem nativeFamily_eq_of_coefficient_localizations (f : Spec (.of R) ⟶ S)
    (F G : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))
    (h : ∀ p : Ideal R, ∀ _ : p.IsMaximal,
      Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R (Localization.AtPrime p))) F =
        Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R (Localization.AtPrime p))) G) :
    F = G := by
  apply HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n f
  apply Homogeneous.IdealLocalizationDetection.GradedHilbert.homogeneousIdeal_eq_of_coefficient_localizations
  intro p hp
  let : p.IsMaximal := hp
  let : Module.Flat R (Localization.AtPrime p) := IsLocalization.flat _ p.primeCompl
  have he := congrArg (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) ≫ f)) (h p hp)
  rw [FlatCoefficientCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat_baseChange, FlatCoefficientCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat_baseChange] at he
  exact he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FamilyLocalizationDetection.GradedHilbert
