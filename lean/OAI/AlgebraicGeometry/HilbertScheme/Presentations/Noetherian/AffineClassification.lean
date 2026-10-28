import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterCoordinates

/-! # Affine Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineClassification.GradedHilbert

noncomputable section

/-! Native polynomial families over every noetherian affine test scheme
have a unique actual parameter on the bounded Hilbert scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem existsUnique_noetherian_affine_hilbert_parameter (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  obtain ⟨x, hx, _⟩ := AffineCoordinateLift.GradedHilbert.existsUnique_noetherian_affine_hilbert_coordinate_lift f F P hP hN hr
  refine ⟨x, AffineParameterFamily.GradedHilbert.noetherianAffine_hilbert_coordinate_lift_family f F P hP hN hr x hx, ?_⟩
  intro y hy
  apply (cancel_mono (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S
    (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))).mp
  exact (AffineParameterCoordinates.GradedHilbert.noetherianAffine_hilbert_parameter_coordinates f F P hP hN hr y hy).trans hx.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineClassification.GradedHilbert
