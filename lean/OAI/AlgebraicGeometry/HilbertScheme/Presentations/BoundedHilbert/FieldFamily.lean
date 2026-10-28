import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldInjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldChartLift

/-! # Field Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldFamily.GradedHilbert

noncomputable section

/-! Canonical field polynomials and injectivity of the universal-family
map for the actual global bounded Hilbert parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S]

theorem boundedHilbertUniversalFamily_chart_family (q : ℕ → ℕ)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) {T : Over S} (x : T ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q) :
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (x ≫ ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q)
        (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q) =
      NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q (x ≫ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)
        ((NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).map x.op (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_universal_mem a S q)) := by
  rw [Hilbert.Functor.pullbackFamily_comp, UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily_restriction]
  exact (NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_baseChange a S q x (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)
    (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_universal_mem a S q)).symm

variable {K : Type u} [Field K]

theorem boundedHilbertUniversalFamily_field_polynomial (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) (f : Spec (.of K) ⟶ S)
    (x : Over.mk f ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q))).toIdeal P := by
  obtain ⟨a, y, hy⟩ := FieldChartLift.GradedHilbert.boundedHilbert_field_chart_lift q f x
  rw [← hy, boundedHilbertUniversalFamily_chart_family]
  exact NormalizedHilbert.FieldPolynomial.GradedHilbert.normalizedHilbertNativeFamily_field_polynomial a f q P hP _ _

theorem boundedHilbertUniversalFamily_field_injective (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) (f : Spec (.of K) ⟶ S) :
    Function.Injective (fun x : Over.mk f ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q =>
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)) := by
  intro x y h
  change Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
    (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q) =
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) y
      (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q) at h
  obtain ⟨a, xa, hxa⟩ := FieldChartLift.GradedHilbert.boundedHilbert_field_chart_lift q f x
  obtain ⟨b, yb, hyb⟩ := FieldChartLift.GradedHilbert.boundedHilbert_field_chart_lift q f y
  rw [← hxa, ← hyb, boundedHilbertUniversalFamily_chart_family,
    boundedHilbertUniversalFamily_chart_family] at h
  apply (cancel_mono (Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S q)).mp
  rw [← hxa, ← hyb, Category.assoc, Category.assoc,
    ChartPullback.GradedHilbert.boundedHilbertChartOverMap_parameter, ChartPullback.GradedHilbert.boundedHilbertChartOverMap_parameter,
    ← Category.assoc, ← Category.assoc]
  exact NormalizedHilbert.FieldInjectivity.GradedHilbert.normalizedHilbertNativeFamily_field_parameter_injective a b f q P hP hN hr _ _ _ _ h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldFamily.GradedHilbert
