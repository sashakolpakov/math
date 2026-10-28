import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineClassification

/-! # Polynomial Parameter Uniqueness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialParameterUniqueness.GradedHilbert

noncomputable section

/-! A native family with its canonical polynomial determines its Hilbert
parameter on every locally noetherian test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {T : Over S} [IsLocallyNoetherian T.left]

theorem noetherian_polynomial_hilbert_parameter_unique
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (x y : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))
    (hx : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F)
    (hy : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) y
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F) :
    x = y := by
  apply Over.OverMorphism.ext
  apply MapStalkDetection.schemeHom_eq_of_fromSpecStalk x.left y.left
  intro t
  let R : Type u := T.left.presheaf.stalk t
  let : IsLocalRing R := inferInstanceAs (IsLocalRing (T.left.presheaf.stalk t))
  let : IsNoetherianRing R := inferInstanceAs (IsNoetherianRing (T.left.presheaf.stalk t))
  let f : Spec (.of R) ⟶ S := T.left.fromSpecStalk t ≫ T.hom
  let b : Over.mk f ⟶ T := Over.homMk (T.left.fromSpecStalk t) rfl
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F
  have hG := (hP.pullback b).affine_residue
  obtain ⟨z, _, hz⟩ := AffineClassification.GradedHilbert.existsUnique_noetherian_affine_hilbert_parameter f G P hG hN hr
  have hxb : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ x)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = G := by
    rw [Hilbert.Functor.pullbackFamily_comp, hx]
  have hyb : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ y)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = G := by
    rw [Hilbert.Functor.pullbackFamily_comp, hy]
  exact congrArg Over.Hom.left ((hz (b ≫ x) hxb).trans (hz (b ≫ y) hyb).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialParameterUniqueness.GradedHilbert
