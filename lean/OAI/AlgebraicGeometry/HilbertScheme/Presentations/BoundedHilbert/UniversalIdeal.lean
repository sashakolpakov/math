import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.BoundedFiberPolynomial

/-! # Universal Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalIdeal.GradedHilbert

noncomputable section

/-! The universal ideal on the bounded Hilbert scheme restricts to the
actual polynomial ideal on each normalized parameter chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u}) [IsLocallyNoetherian S] (q : ℕ → ℕ)

theorem normalizedHilbertNativeFamily_original_ker {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T)) :
    (NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx).val =
      (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion (Normalized.Chart.Grassmannian.normalizedChart a S)
        (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)) x).ker := by
  let : IsLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Normalized.Chart.Grassmannian.normalizedChart a S).hom
  exact Global.PolynomialInclusion.GradedHilbert.globalBoundedPolynomialFamily_val (Normalized.Chart.Grassmannian.normalizedChart a S) x (NormalizedHilbert.Chart.GradedHilbert.universalPolynomialGenerators a S) N
    (NormalizedHilbert.Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S) q
    (DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_flat (Normalized.Chart.Grassmannian.normalizedChart a S) (NormalizedHilbert.Chart.GradedHilbert.universalPolynomialGenerators a S) N
      (NormalizedHilbert.Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S) q x hx)

theorem boundedHilbertUniversalFamily_chart_ideal {T : Over S} (x : T ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q) :
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (x ≫ ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q)
      (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)).val =
      (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion (Normalized.Chart.Grassmannian.normalizedChart a S)
        (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S))
        (x ≫ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)).ker := by
  rw [Hilbert.Functor.pullbackFamily_comp, UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily_restriction]
  dsimp only [UniversalCompatibility.GradedHilbert.boundedHilbertChartUniversalFamily]
  rw [← NormalizedHilbert.IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_baseChange]
  exact normalizedHilbertNativeFamily_original_ker a S q _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalIdeal.GradedHilbert
