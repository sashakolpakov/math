import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScaledTwistHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FamilyPolynomialBounds

/-! # Scaled Polynomial Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScaledPolynomialBounds

noncomputable section

/-! A fixed scaling of source twists gives a finite Hilbert-polynomial
bound on all field fibers of a noetherian projective family. The finite
set is selected before the field, fiber, or second embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_finite_scaled_fiber_polynomials
    {R : Type} [CommRing R] [IsNoetherianRing R] {n : ℕ} {X : Scheme.{0}}
    (f : X ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left) [IsClosedImmersion f]
    (c : ℕ) (hc : 0 < c) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (k : Type) [Field k] (φ : R →+* k) (Y : Scheme.{0})
        (j : Y ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace k n).left) (a : Y ⟶ X),
        IsPullback a j f (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n) →
        ∀ (m : ℕ) (g : Y ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k m)) [IsClosedImmersion g],
          g ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) = j ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) →
          (∀ d : ℕ, Nonempty
            ((Scheme.Modules.pullback g).obj (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) 0 d) ≅
              (Scheme.Modules.pullback j).obj
                (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) 0 (c * d)))) →
          ∃ P ∈ F, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf g.ker).toIdeal P := by
  classical
  obtain ⟨F, hF⟩ := Projective.FamilyPolynomialBounds.PolarizationEmbedding.exists_finite_closed_projective_fiber_polynomials f
  refine ⟨F.image (fun P => P.comp (Polynomial.C (c : ℚ) * Polynomial.X)), ?_⟩
  intro k hk φ Y j a H m g hg hb hL
  have : IsClosedImmersion j := MorphismProperty.of_isPullback H inferInstance
  obtain ⟨P, hPF, hP⟩ := hF k φ Y j a H
  exact ⟨P.comp (Polynomial.C (c : ℚ) * Polynomial.X), Finset.mem_image.mpr ⟨P, hPF, rfl⟩,
    ScaledTwistHilbertPolynomial.PolarizationEmbedding.e34HilbertPolynomial_of_scaled_twists j g hb c hc hL P hP⟩

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScaledPolynomialBounds
