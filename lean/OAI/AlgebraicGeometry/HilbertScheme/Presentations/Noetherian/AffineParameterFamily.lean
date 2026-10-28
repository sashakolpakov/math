import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineCoordinateLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FamilyLocalizationDetection

/-! # Affine Parameter Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterFamily.GradedHilbert

noncomputable section

/-! The actual universal family at the global noetherian affine Hilbert
coordinate lift is exactly the native family used to construct that lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem noetherianAffine_hilbert_coordinate_lift_family (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))
    (hx : x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =
      Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr) :
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  apply Intrinsic.FamilyLocalizationDetection.GradedHilbert.nativeFamily_eq_of_coefficient_localizations f
  intro p hp
  let : p.IsMaximal := hp
  let A := Localization.AtPrime p
  let φ := algebraMap R A
  let g : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom φ) ≫ f
  let b := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F
  have hG := IntrinsicCoefficientBaseChange.GradedHilbert.noetherian_canonical_residue_polynomial_baseChange f F P hP φ
  obtain ⟨y, hy⟩ := LocalParameter.GradedHilbert.exists_noetherian_local_hilbert_parameter g G P hG N hN ι hr
  have hyc := Local.ParameterCoordinates.GradedHilbert.noetherianLocal_hilbert_parameter_coordinates g G P hG hN hr y hy
  have hn := Intrinsic.AffineGrassmannianNaturality.GradedHilbert.nativeAffineHilbertGrassmannianPoint_natural f F P hP N hN ι hr φ
  let j := BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  have hc : (b ≫ x) ≫ j = y ≫ j := by
    rw [Category.assoc, hx, hn, hyc]
  have he : b ≫ x = y := (cancel_mono j).mp hc
  change Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))) = G
  rw [← Hilbert.Functor.pullbackFamily_comp, he]
  exact hy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterFamily.GradedHilbert
