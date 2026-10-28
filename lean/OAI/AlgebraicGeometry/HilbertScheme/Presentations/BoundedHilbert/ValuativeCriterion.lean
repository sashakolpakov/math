import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationParameterFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Immersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Valuative Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ValuativeCriterion.GradedHilbert

noncomputable section

/-! The constructed bounded Hilbert scheme satisfies the actual valuative
existence criterion, by valuation closure and uniqueness of field parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S]

theorem boundedHilbert_valuative_existence (P : Polynomial ℚ)
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ValuativeCriterion.Existence
      (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).hom := by
  intro D
  let q := Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P
  let H := Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q
  let k := Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))
  let y : Over.mk (k ≫ D.i₂) ⟶ H := Over.homMk D.i₁ D.commSq.w
  let F := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) y
    (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)
  have hF : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (k ≫ D.i₂) F).toIdeal P :=
    FieldFamily.GradedHilbert.boundedHilbertUniversalFamily_field_polynomial q P hP _ y
  obtain ⟨x, hx⟩ := ValuationParameterFamily.GradedHilbert.exists_valuation_hilbert_parameter_generic_family D.i₂ F P hF N hN ι hr
  have he : Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap D.i₂ (algebraMap D.R D.K) ≫ x = y :=
    FieldFamily.GradedHilbert.boundedHilbertUniversalFamily_field_injective q P hP hN hr (k ≫ D.i₂) hx
  exact ⟨⟨{
    l := x.left
    fac_left := congrArg Over.Hom.left he
    fac_right := x.w }⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ValuativeCriterion.GradedHilbert
