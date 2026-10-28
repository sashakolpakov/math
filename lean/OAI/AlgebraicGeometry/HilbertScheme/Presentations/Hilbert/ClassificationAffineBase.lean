import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryAffineClassification

/-! # Classification Affine Base -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClassificationAffineBase.GradedHilbert

noncomputable section

/-! Hilbert classification over arbitrary test schemes whose structural
map factors through a Noetherian affine scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {B : Type u} [CommRing B] [IsNoetherianRing B]
variable {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι] {T : Over S}

theorem existsUnique_hilbert_parameter_of_affine_base
    (c : Spec (.of B) ⟶ S) (d : T.left ⟶ Spec (.of B)) (hd : d ≫ c = T.hom)
    (F : Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T)
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let C := T.left.affineOpenCover
  let U (i : C.I₀) : Over S := Over.mk (C.f i ≫ T.hom)
  let b (i : C.I₀) : U i ⟶ T := Over.homMk (C.f i) rfl
  let : ∀ i, IsOpenImmersion (b i).left := fun i => inferInstanceAs (IsOpenImmersion (C.f i))
  apply ParameterOpenCoverGluing.GradedHilbert.hilbert_parameter_of_openCover F P hP hN hr U b (fun t => C.openCover.exists_eq t)
  intro i
  let A : Type u := C.X i
  let j : Spec (.of A) ⟶ T.left := C.f i
  let φ : B →+* A := (Spec.preimage (j ≫ d)).hom
  let : Algebra B A := φ.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ c = j ≫ T.hom := by
    change Spec.map (Spec.preimage (j ≫ d)) ≫ c = _
    rw [Spec.map_preimage, Category.assoc, hd]
  exact (ArbitraryAffineClassification.GradedHilbert.existsUnique_affine_hilbert_parameter_of_base_factorization c (j ≫ T.hom) ha
    (Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b i) F) P (hP.pullback (b i)) hN hr).exists

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClassificationAffineBase.GradedHilbert
