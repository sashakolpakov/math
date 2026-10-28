import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HilbertSections

/-! # Projective Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveHilbertPolynomial

noncomputable section

/-! Closed embeddings whose native twists pull back to the same source
bundles have one common Hilbert polynomial. The base morphism is retained
so that all comparisons are linear over the same coefficient ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}

def nativeTwistSectionsFixedEquiv
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (π : X ⟶ Spec (.of R)) (hπ : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) = π)
    (j : Fin (n + 1)) (m : ℕ) (L : X.Modules)
    (e : (Scheme.Modules.pullback f).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≅ L) :
    (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R))).obj
      ((Scheme.Modules.pullback f).obj
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) ≃ₗ[Γ(Spec (.of R), ⊤)]
          (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj L :=
  ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R))).mapIso e).toLinearEquiv |>.trans
    (((eqToIso (congrArg (fun q => SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor q) hπ)).app L).toLinearEquiv)

theorem exists_fixed_nativeHilbertPolynomial [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {ι : Type v} [Nonempty ι]
    (f : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
    [∀ a, IsClosedImmersion (f a)]
    (π : X ⟶ Spec (.of R)) (hπ : ∀ a, f a ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) = π)
    (j : Fin (n + 1)) (L : ℕ → X.Modules)
    (hL : ∀ a m, Nonempty ((Scheme.Modules.pullback (f a)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≅ L m)) :
    ∃ P : Polynomial ℚ, ∀ a, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a)).toIdeal P := by
  classical
  let := hfield.toField
  let a₀ : ι := Classical.choice inferInstance
  obtain ⟨P, c, hc⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a₀))
  obtain ⟨b, hb⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections (f a₀) j
  have hd (a : ι) (m : ℕ) :=
    (nativeTwistSectionsFixedEquiv (f a) π (hπ a) j m (L m) (Classical.choice (hL a m))).finrank_eq
  refine ⟨P, fun a => ?_⟩
  obtain ⟨d, hd'⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections (f a) j
  refine ⟨max d (max b c), fun m hm => ?_⟩
  have hdm := (le_max_left d (max b c)).trans hm
  have hbm := (le_max_left b c).trans ((le_max_right d (max b c)).trans hm)
  have hcm := (le_max_right b c).trans ((le_max_right d (max b c)).trans hm)
  have he : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a)).toIdeal m =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a₀)).toIdeal m :=
    (hd' m hdm).trans ((hd a m).trans ((hd a₀ m).symm.trans (hb m hbm).symm))
  rw [he]
  exact hc m hcm

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveHilbertPolynomial
