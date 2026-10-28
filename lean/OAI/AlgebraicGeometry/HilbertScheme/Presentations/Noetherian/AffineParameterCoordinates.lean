import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MapStalkDetection

/-! # Affine Parameter Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterCoordinates.GradedHilbert

noncomputable section

/-! The Grassmannian coordinates of any actual Hilbert parameter over a
noetherian affine test scheme are the canonical coordinates of its family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem noetherianAffine_hilbert_parameter_coordinates (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))
    (hx : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F) :
    x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =
      Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr := by
  apply Over.OverMorphism.ext
  apply MapStalkDetection.schemeHom_eq_of_fromSpecStalk (X := Spec (.of R))
  intro p
  let A : Type u := (Spec (.of R)).presheaf.stalk p
  let : IsLocalRing A := inferInstanceAs (IsLocalRing ((Spec (.of R)).presheaf.stalk p))
  let : IsNoetherianRing A := inferInstanceAs (IsNoetherianRing ((Spec (.of R)).presheaf.stalk p))
  let φ : R →+* A := (StructureSheaf.toStalk (CommRingCat.of R) p).hom
  let g : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom φ) ≫ f
  let b := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F
  have hG := IntrinsicCoefficientBaseChange.GradedHilbert.noetherian_canonical_residue_polynomial_baseChange f F P hP φ
  have hxG : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ x)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = G := by
    rw [Hilbert.Functor.pullbackFamily_comp, hx]
  have hc := Local.ParameterCoordinates.GradedHilbert.noetherianLocal_hilbert_parameter_coordinates g G P hG hN hr (b ≫ x) hxG
  have hn := Intrinsic.AffineGrassmannianNaturality.GradedHilbert.nativeAffineHilbertGrassmannianPoint_natural f F P hP N hN ι hr φ
  have he : b ≫ (x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S
      (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) =
        b ≫ Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr := by
    rw [← Category.assoc, hc, hn]
  change (Spec (.of R)).fromSpecStalk p ≫
    (x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).left =
      (Spec (.of R)).fromSpecStalk p ≫ (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr).left
  rw [Spec.fromSpecStalk_eq']
  exact congrArg Over.Hom.left he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterCoordinates.GradedHilbert
