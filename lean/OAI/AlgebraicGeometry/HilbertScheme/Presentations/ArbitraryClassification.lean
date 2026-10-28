import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClassificationAffineBase

/-! # Arbitrary Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryClassification.GradedHilbert

noncomputable section

/-! The actual bounded Hilbert scheme classifies native projective families
on every test scheme, with no Noetherian hypothesis on the tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {T : Over S}

theorem existsUnique_arbitrary_scheme_hilbert_parameter
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let C := S.affineOpenCover
  let D : T.left.OpenCover.{u} := C.openCover.pullback₁ T.hom
  let U (i : D.I₀) : Over S := Over.mk (D.f i ≫ T.hom)
  let b (i : D.I₀) : U i ⟶ T := Over.homMk (D.f i) rfl
  let : ∀ i, IsOpenImmersion (b i).left := fun i => inferInstanceAs (IsOpenImmersion (D.f i))
  apply Hilbert.ParameterOpenCoverGluing.GradedHilbert.hilbert_parameter_of_openCover F P hP hN hr U b (fun t => D.exists_eq t)
  intro i
  change C.I₀ at i
  let B : Type u := C.X i
  let : IsNoetherianRing B := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (C.f i))
  let c : Spec (.of B) ⟶ S := C.f i
  let d : (U i).left ⟶ Spec (.of B) := C.openCover.pullbackHom T.hom i
  have hd : d ≫ c = (U i).hom := C.openCover.pullbackHom_map T.hom i
  exact (Hilbert.ClassificationAffineBase.GradedHilbert.existsUnique_hilbert_parameter_of_affine_base c d hd
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b i) F) P (hP.pullback (b i)) hN hr).exists

theorem existsUnique_arbitrary_exact_hilbert_parameter
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (P : Polynomial ℚ)
    (hP : Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F :=
  existsUnique_arbitrary_scheme_hilbert_parameter F P
    (ExactCanonicalFiberPolynomial.GradedHilbert.canonicalFiberHilbertPolynomial_of_hasFiberHilbertPolynomial F P hP) hN hr

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryClassification.GradedHilbert
