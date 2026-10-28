import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal

/-! # Varying Projective Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.VaryingProjectiveHilbertPolynomial

noncomputable section

/-! Fixed native twist pullbacks give one Hilbert polynomial even when the
projective ambient is allowed to vary. This keeps the polynomial independent
of the Segre presentation later chosen by the Presentations existence theorem. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_fixed_varying_nativeHilbertPolynomial
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {ι : Type v} [Nonempty ι] (n : ι → ℕ)
    (f : ∀ a, X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R (n a))) [∀ a, IsClosedImmersion (f a)]
    (π : X ⟶ Spec (.of R)) (hπ : ∀ a, f a ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) = π)
    (j : ∀ a, Fin (n a + 1)) (L : ℕ → X.Modules)
    (hL : ∀ a m, Nonempty ((Scheme.Modules.pullback (f a)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (j a) m) ≅ L m)) :
    ∃ P : Polynomial ℚ, ∀ a, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a)).toIdeal P := by
  classical
  let := hfield.toField
  let a₀ : ι := Classical.choice inferInstance
  obtain ⟨P, c, hc⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a₀))
  obtain ⟨b, hb⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections (f a₀) (j a₀)
  have hd (a : ι) (m : ℕ) :=
    (Fixed.ProjectiveHilbertPolynomial.PolarizationEmbedding.nativeTwistSectionsFixedEquiv (f a) π (hπ a) (j a) m (L m) (Classical.choice (hL a m))).finrank_eq
  refine ⟨P, fun a => ?_⟩
  obtain ⟨d, hd'⟩ := Projective.HilbertSections.PolarizationEmbedding.eventually_nativeHilbertFunction_eq_sections (f a) (j a)
  refine ⟨max d (max b c), fun m hm => ?_⟩
  have hdm := (le_max_left d (max b c)).trans hm
  have hbm := (le_max_left b c).trans ((le_max_right d (max b c)).trans hm)
  have hcm := (le_max_right b c).trans ((le_max_right d (max b c)).trans hm)
  have he : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a)).toIdeal m =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal (f a₀)).toIdeal m :=
    (hd' m hdm).trans ((hd a m).trans ((hd a₀ m).symm.trans (hb m hbm).symm))
  rw [he]
  exact hc m hcm

theorem exists_fixed_varying_e34HilbertPolynomial
    {k : Type u} [Field k] {X : Scheme.{u}} {ι : Type v} [Nonempty ι] (n : ι → ℕ)
    (f : ∀ a, X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k (n a))) [∀ a, IsClosedImmersion (f a)]
    (π : X ⟶ Spec (.of k)) (hπ : ∀ a, f a ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) = π)
    (j : ∀ a, Fin (n a + 1)) (L : ℕ → X.Modules)
    (hL : ∀ a m, Nonempty ((Scheme.Modules.pullback (f a)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) (j a) m) ≅ L m)) :
    ∃ P : Polynomial ℚ, ∀ a, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (f a).ker).toIdeal P := by
  have hfield : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  obtain ⟨P, hP⟩ := exists_fixed_varying_nativeHilbertPolynomial hfield n f π hπ j L hL
  exact ⟨P, fun a => (Presentations.IntrinsicCoordinateIdeal.PolarizationEmbedding.native_hasHilbertPolynomial_iff_e34 (f a) P).mp (hP a)⟩

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.VaryingProjectiveHilbertPolynomial
