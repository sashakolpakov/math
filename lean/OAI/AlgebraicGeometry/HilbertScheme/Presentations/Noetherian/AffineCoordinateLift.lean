import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ParameterCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannianNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.StalkFactorization

/-! # Affine Coordinate Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineCoordinateLift.GradedHilbert

noncomputable section

/-! The canonical Grassmannian point of any native noetherian affine
family factors uniquely through the actual bounded Hilbert scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem existsUnique_noetherian_affine_hilbert_coordinate_lift (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =
        Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr := by
  let : IsLocallyNoetherian (Over.mk f).left := inferInstanceAs (IsLocallyNoetherian (Spec (.of R)))
  let : LocallyOfFiniteType
      (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).left :=
    inferInstanceAs (LocallyOfFiniteType
      (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)))
  apply StalkFactorization.over_lift_of_fromSpecStalk (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr)
    (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))
  intro p
  let A : Type u := (Spec (.of R)).presheaf.stalk p
  let : IsLocalRing A := inferInstanceAs (IsLocalRing ((Spec (.of R)).presheaf.stalk p))
  let : IsNoetherianRing A := inferInstanceAs (IsNoetherianRing ((Spec (.of R)).presheaf.stalk p))
  let φ : R →+* A := (StructureSheaf.toStalk (CommRingCat.of R) p).hom
  let g : Spec (.of A) ⟶ S := Spec.map (CommRingCat.ofHom φ) ≫ f
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F
  have hG := IntrinsicCoefficientBaseChange.GradedHilbert.noetherian_canonical_residue_polynomial_baseChange f F P hP φ
  obtain ⟨x, hx⟩ := Local.ParameterCoordinates.GradedHilbert.exists_noetherianLocal_hilbert_coordinate_lift g G P hG hN hr
  have hn := Intrinsic.AffineGrassmannianNaturality.GradedHilbert.nativeAffineHilbertGrassmannianPoint_natural f F P hP N hN ι hr φ
  refine ⟨x.left, ?_⟩
  change x.left ≫ (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).left =
    (Spec (.of R)).fromSpecStalk p ≫ (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr).left
  rw [Spec.fromSpecStalk_eq']
  exact congrArg Over.Hom.left (hx.trans hn.symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineCoordinateLift.GradedHilbert
