import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.Classification

/-! # Polynomial Equivalence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialEquivalence.GradedHilbert

noncomputable section

/-! The constructed universal family gives an actual equivalence with
canonical polynomial families on every locally noetherian test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem boundedHilbertUniversalFamily_canonicalFiberPolynomial
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)
    {T : Over S} (x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) :
    CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)) P := by
  intro K _ a
  let b : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (a ≫ T.hom)
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)))).toIdeal P
  rw [← Hilbert.Functor.pullbackFamily_comp]
  exact BoundedHilbert.FieldFamily.GradedHilbert.boundedHilbertUniversalFamily_field_polynomial q P hP _ (b ≫ x)

def noetherianHilbertPolynomialEquiv
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (T : Over S) [IsLocallyNoetherian T.left] :
    (T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) ≃
      {F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T // CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P} := by
  let f : (T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) →
      {F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T // CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P} :=
    fun x => ⟨Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)),
      boundedHilbertUniversalFamily_canonicalFiberPolynomial _ P hP x⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact PolynomialParameterUniqueness.GradedHilbert.noetherian_polynomial_hilbert_parameter_unique (f x).val P (f x).property hN hr x y
      rfl (congrArg Subtype.val h).symm
  · intro F
    obtain ⟨x, hx, _⟩ := Classification.GradedHilbert.existsUnique_noetherian_scheme_hilbert_parameter F.val P F.property hN hr
    exact ⟨x, Subtype.ext hx⟩

theorem noetherianHilbertPolynomialEquiv_apply
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (T : Over S) [IsLocallyNoetherian T.left]
    (x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) :
    (noetherianHilbertPolynomialEquiv P hP hN hr T x).val =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) := rfl

theorem noetherianHilbertPolynomialEquiv_natural
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    {T T' : Over S} [IsLocallyNoetherian T.left] [IsLocallyNoetherian T'.left]
    (b : T' ⟶ T)
    (x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) :
    (noetherianHilbertPolynomialEquiv P hP hN hr T' (b ≫ x)).val =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b
        (noetherianHilbertPolynomialEquiv P hP hN hr T x).val :=
  Hilbert.Functor.pullbackFamily_comp (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b x _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialEquivalence.GradedHilbert
