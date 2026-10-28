import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalClassification
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PrimePointSpreading
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpreadParameterFamilyRefinement
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.StructureProperties

/-! # Parameter Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ParameterNeighborhood.GradedHilbert

noncomputable section

/-! Every coefficient prime of an arbitrary affine Hilbert test has an
open neighborhood carrying its actual bounded Hilbert parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {B A : Type u} [CommRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
variable {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem exists_hilbert_parameter_neighborhood_of_base_factorization
    (c : Spec (.of B) ⟶ S) (a : Spec (.of A) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ c = a)
    (F : Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) (p : PrimeSpectrum A) :
    ∃ (V : Over S) (b : V ⟶ Over.mk a), IsOpenImmersion b.left ∧ p ∈ Set.range b.left ∧
      ∃ x : V ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
        Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
          (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) =
        Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F := by
  let Ap := Localization.AtPrime p.asIdeal
  let ap : Spec (.of Ap) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A Ap)) ≫ a
  let bp := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A Ap)
  let Fp := Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) bp F
  obtain ⟨xp, hxp⟩ := ArbitraryLocalClassification.GradedHilbert.exists_arbitrary_local_hilbert_parameter ap Fp P (hP.pullback bp) hN hr
  let H := BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let U := BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  obtain ⟨s, hs, j, hj, hjbase⟩ := Relative.PrimePointSpreading.spread_relative_prime_point H c a ha p.asIdeal xp.left xp.w
  let xs : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ a) ⟶ H :=
    Over.homMk j hjbase
  exact SpreadParameterFamilyRefinement.GradedHilbert.refine_spread_family_parameter a F H U p xp hxp s hs xs hj

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ParameterNeighborhood.GradedHilbert
