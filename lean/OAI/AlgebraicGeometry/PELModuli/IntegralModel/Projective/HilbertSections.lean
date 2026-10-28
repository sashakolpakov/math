import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicCoordinateIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Hilbert Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HilbertSections

noncomputable section

/-! For a closed projective subscheme, the actual homogeneous coordinate
quotients agree with native twist sections in sufficiently large degree.
The Hilbert polynomial therefore measures those actual sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [QuasiCompact f]

theorem nativePolynomialRestriction_ker (j : Fin (n + 1)) (m : ℕ) :
    (PolynomialRestriction.PolarizationEmbedding.nativePolynomialRestriction f j m).ker =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal m := by
  ext p
  exact IntrinsicCoordinateIdeal.PolarizationEmbedding.nativePolynomialRestriction_zero_iff_mem_coordinateIdeal f j m p

def nativeCoordinateQuotientSectionsEquiv (j : Fin (n + 1)) (m : ℕ)
    (h : Function.Surjective (PolynomialRestriction.PolarizationEmbedding.nativePolynomialRestriction f j m)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal m ≃ₗ[Γ(Spec (.of R), ⊤)]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R))).obj
        ((Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) :=
  (Submodule.quotEquivOfEq _ _ (nativePolynomialRestriction_ker f j m).symm).trans
    ((PolynomialRestriction.PolarizationEmbedding.nativePolynomialRestriction f j m).quotKerEquivOfSurjective h)

theorem eventually_nativeHilbertFunction_eq_sections [IsNoetherianRing R] [IsClosedImmersion f]
    (j : Fin (n + 1)) :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal m =
        Module.finrank Γ(Spec (.of R), ⊤)
          ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R))).obj
            ((Scheme.Modules.pullback f).obj
              (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m))) := by
  obtain ⟨b, hb⟩ := PolynomialRestriction.PolarizationEmbedding.eventually_nativePolynomialRestriction_surjective f j
  exact ⟨b, fun m hm => (nativeCoordinateQuotientSectionsEquiv f j m (hb m hm)).finrank_eq⟩

theorem nativeTwistSections_eventuallyPolynomial [IsNoetherianRing R] [IsClosedImmersion f]
    (j : Fin (n + 1)) (hfield : IsField Γ(Spec (.of R), ⊤)) :
    ∃ P : Polynomial ℚ,
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal P ∧
      ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
        (Module.finrank Γ(Spec (.of R), ⊤)
          ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R))).obj
            ((Scheme.Modules.pullback f).obj
              (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m))) : ℚ) =
                P.eval (m : ℚ) := by
  let := hfield.toField
  obtain ⟨P, hP⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f)
  obtain ⟨b, hb⟩ := eventually_nativeHilbertFunction_eq_sections f j
  obtain ⟨c, hc⟩ := hP
  refine ⟨P, ⟨c, hc⟩, max b c, fun m hm => ?_⟩
  rw [← hb m ((le_max_left b c).trans hm)]
  exact hc m ((le_max_right b c).trans hm)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HilbertSections
