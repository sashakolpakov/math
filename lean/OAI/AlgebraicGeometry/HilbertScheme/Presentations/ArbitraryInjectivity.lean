import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalInjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalSpectraDetection

/-! # Arbitrary Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryInjectivity.GradedHilbert

noncomputable section

/-! Hilbert parameters are uniquely determined by their actual native
families on every test scheme, without a noetherianity assumption on tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem boundedHilbertUniversalFamily_injective
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (T : Over S) :
    Function.Injective (fun x : T ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S
        (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =>
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply LocalSpectraDetection.schemeHom_eq_of_localSpectra x.left y.left
  intro t
  let R : Type u := T.left.presheaf.stalk t
  let : IsLocalRing R := inferInstanceAs (IsLocalRing (T.left.presheaf.stalk t))
  let f : Spec (.of R) ⟶ S := T.left.fromSpecStalk t ≫ T.hom
  let b : Over.mk f ⟶ T := Over.homMk (T.left.fromSpecStalk t) rfl
  have hb : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ x)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) =
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (b ≫ y)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) := by
    rw [Hilbert.Functor.pullbackFamily_comp, Hilbert.Functor.pullbackFamily_comp]
    exact congrArg (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b) h
  exact congrArg Over.Hom.left
    (ArbitraryLocalInjectivity.GradedHilbert.boundedHilbertUniversalFamily_arbitrary_local_injective P hP hN hr f hb)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryInjectivity.GradedHilbert
