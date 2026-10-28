import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.IntrinsicFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartPullback

/-! # Universal Compatibility -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalCompatibility.GradedHilbert

noncomputable section

/-! The native universal families on the bounded Hilbert charts agree on
the actual intersections of those charts in the constructed parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (S : Scheme.{u}) [IsLocallyNoetherian S] (q : ℕ → ℕ)

theorem normalizedHilbertNativeFamily_same_parameter
    (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) {T : Over S}
    (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (y : T ⟶ Normalized.Chart.Grassmannian.normalizedChart b S)
    (hx : x ∈ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T))
    (hy : y ∈ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).obj (.op T))
    (h : x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = y ≫ Grassmannian.Gluing.grassmannianChartOverMap b S) :
    NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx = NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily b S q y hy := by
  let hp := NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedGrassmannianOverlap_isPullback_over a b S
  let w := hp.lift x y h
  have hw₁ : w ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = x := hp.lift_fst _ _ h
  have hw₂ : w ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S = y :=
    hp.lift_snd _ _ h
  have he := NormalizedHilbert.OverlapCriterion.GradedHilbert.normalizedOverlap_polynomialIdeal a b S w
  rw [hw₁, hw₂] at he
  apply Subtype.ext
  rw [NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_val, NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_val, he]

def boundedHilbertChartUniversalFamily (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q) :=
  NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)
    (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_universal_mem a S q)

theorem boundedHilbertChartUniversalFamily_overlap (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (pullback.fst (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) (ChartPullback.GradedHilbert.boundedHilbertChartOverMap b S q))
        (boundedHilbertChartUniversalFamily S q a) =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (pullback.snd (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) (ChartPullback.GradedHilbert.boundedHilbertChartOverMap b S q))
        (boundedHilbertChartUniversalFamily S q b) := by
  dsimp only [boundedHilbertChartUniversalFamily]
  rw [← NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_baseChange, ← NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_baseChange]
  apply normalizedHilbertNativeFamily_same_parameter
  have h := congrArg (fun f => f ≫ Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S q)
    (pullback.condition (f := ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q) (g := ChartPullback.GradedHilbert.boundedHilbertChartOverMap b S q))
  simp only [Category.assoc, ChartPullback.GradedHilbert.boundedHilbertChartOverMap_parameter] at h
  exact h

instance boundedHilbertChartOverMap_isOpenImmersion (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    IsOpenImmersion (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q).left :=
  inferInstanceAs (IsOpenImmersion (Data.GradedHilbert.boundedHilbertChartMap n N S q a))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalCompatibility.GradedHilbert
