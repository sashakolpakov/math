import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalClassification

/-! # Arbitrary Polynomial Parameter Uniqueness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryPolynomialParameterUniqueness.GradedHilbert

noncomputable section

/-! An actual native family and its canonical polynomial determine its
Hilbert parameter over every test scheme, including arbitrary nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {T : Over S}

theorem polynomial_hilbert_parameter_unique
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
  apply LocalSpectraDetection.schemeHom_eq_of_localSpectra x.left y.left
  intro t
  let R : Type u := T.left.presheaf.stalk t
  let : IsLocalRing R := inferInstanceAs (IsLocalRing (T.left.presheaf.stalk t))
  let f : Spec (.of R) ⟶ S := T.left.fromSpecStalk t ≫ T.hom
  let b : Over.mk f ⟶ T := Over.homMk (T.left.fromSpecStalk t) rfl
  let G := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F
  obtain ⟨z, _, hz⟩ := ArbitraryLocalClassification.GradedHilbert.existsUnique_arbitrary_local_hilbert_parameter f G P (hP.pullback b) hN hr
  have hxb : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ x)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = G := by
    rw [Hilbert.Functor.pullbackFamily_comp, hx]
  have hyb : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ y)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = G := by
    rw [Hilbert.Functor.pullbackFamily_comp, hy]
  exact congrArg Over.Hom.left ((hz (b ≫ x) hxb).trans (hz (b ≫ y) hyb).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryPolynomialParameterUniqueness.GradedHilbert
