import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ParameterNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ParameterOpenCoverGluing

/-! # Arbitrary Affine Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryAffineClassification.GradedHilbert

noncomputable section

/-! Native Hilbert families over arbitrary affine test rings are classified
once their base map is expressed through a Noetherian affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {B A : Type u} [CommRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
variable {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem existsUnique_affine_hilbert_parameter_of_base_factorization
    (c : Spec (.of B) ⟶ S) (a : Spec (.of A) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ c = a)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : Over.mk a ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  classical
  choose U b hO hcover x hx using
    fun p : PrimeSpectrum A => Hilbert.ParameterNeighborhood.GradedHilbert.exists_hilbert_parameter_neighborhood_of_base_factorization c a ha F P hP hN hr p
  let : ∀ p, IsOpenImmersion (b p).left := hO
  apply Hilbert.ParameterOpenCoverGluing.GradedHilbert.hilbert_parameter_of_openCover F P hP hN hr U b _ (fun p => ⟨x p, hx p⟩)
  intro t
  let p : PrimeSpectrum A := t
  obtain ⟨y, hy⟩ := hcover p
  exact ⟨p, y, hy⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryAffineClassification.GradedHilbert
