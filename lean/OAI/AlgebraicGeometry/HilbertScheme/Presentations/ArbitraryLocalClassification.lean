import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalParameter
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RingPointOpenLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactCanonicalFiberPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryInjectivity

/-! # Arbitrary Local Classification -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalClassification.GradedHilbert

noncomputable section

/-! Full existence and uniqueness of exact Hilbert parameters over every
local test ring, with no Noetherian hypothesis on that ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem exists_arbitrary_local_hilbert_parameter
    (a : Spec (.of A) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ x : Over.mk a ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let C := S.affineOpenCover
  obtain ⟨i, b, hb⟩ := Local.RingPointOpenLift.localRingPoint_lift_openCover C.openCover a
  change C.I₀ at i
  change Spec (.of A) ⟶ Spec (C.X i) at b
  change b ≫ C.f i = a at hb
  let B : Type u := C.X i
  let : IsNoetherianRing B := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (C.f i))
  let φ : B →+* A := (Spec.preimage b).hom
  let : Algebra B A := φ.toAlgebra
  let c : Spec (.of B) ⟶ S := C.f i
  apply ArbitraryLocalParameter.GradedHilbert.exists_local_hilbert_parameter_of_base_factorization c a _ F P hP hN hr
  change Spec.map (Spec.preimage b) ≫ C.f i = a
  rwa [Spec.map_preimage]

theorem existsUnique_arbitrary_local_hilbert_parameter
    (a : Spec (.of A) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : Over.mk a ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  obtain ⟨x, hx⟩ := exists_arbitrary_local_hilbert_parameter a F P hP hN hr
  let p : PrimeSpectrum A := IsLocalRing.closedPoint A
  let J := Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F))
  have hreal : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P :=
    Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile_realizes J (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _) P
      (hP.affine_residue p) N ((le_max_right _ _).trans hN)
  exact ⟨x, hx, fun y hy => ArbitraryInjectivity.GradedHilbert.boundedHilbertUniversalFamily_injective P hreal hN hr
    (Over.mk a) (hy.trans hx.symm)⟩

theorem existsUnique_arbitrary_local_exact_hilbert_parameter
    (a : Spec (.of A) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (P : Polynomial ℚ)
    (hP : Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃! x : Over.mk a ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F :=
  existsUnique_arbitrary_local_hilbert_parameter a F P
    (ExactCanonicalFiberPolynomial.GradedHilbert.canonicalFiberHilbertPolynomial_of_hasFiberHilbertPolynomial F P hP) hN hr

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalClassification.GradedHilbert
