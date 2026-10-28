import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Representation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFactorization

/-! # Chart Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartRestriction.GradedHilbert

noncomputable section

/-! Restricting the glued bounded parameter functor to a Grassmannian chart
recovers exactly its previously constructed Hilbert chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u}) (q : ℕ → ℕ)

theorem boundedHilbertLocalCondition_of_chart {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T)) :
    Representation.GradedHilbert.boundedHilbertLocalCondition n N S q (x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S) := by
  obtain ⟨y, hy, _⟩ := (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_factorization_iff a S q x).mp hx
  refine ⟨Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 T.left), ?_⟩
  intro i
  refine ⟨a, y.left, ?_⟩
  change y.left ≫ ((NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left ≫ (Grassmannian.Gluing.grassmannianChartOverMap a S).left) =
    (𝟙 T.left) ≫ (x.left ≫ (Grassmannian.Gluing.grassmannianChartOverMap a S).left)
  rw [Category.id_comp, ← Category.assoc]
  exact congrArg (fun f => f ≫ (Grassmannian.Gluing.grassmannianChartOverMap a S).left) (congrArg Over.Hom.left hy)

theorem boundedHilbertLocalCondition_chart_iff {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    Representation.GradedHilbert.boundedHilbertLocalCondition n N S q (x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S) ↔
      x ∈ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T) := by
  refine ⟨?_, boundedHilbertLocalCondition_of_chart a S q x⟩
  rintro ⟨V, hV⟩
  obtain ⟨g, hg, _⟩ := Local.MorphismFactorization.lift_of_openCover V x.left (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left (by
    intro i
    obtain ⟨b, k, hk⟩ := hV i
    let Ti : Over S := Over.mk (V.f i ≫ T.hom)
    let vi : Ti ⟶ T := Over.homMk (V.f i)
    have hk' : k ≫ (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q).left =
        (vi ≫ (x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S)).left := hk
    let yi := OverFactorization.overHomOfFactorization k (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q)
      (vi ≫ (x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S)) hk'
    have hyi : yi ≫ NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q = vi ≫ (x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S) :=
      OverFactorization.overHomOfFactorization_comp k (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q)
        (vi ≫ (x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S)) hk'
    have hi : (vi ≫ x) ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = yi ≫ NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q :=
      (Category.assoc _ _ _).trans hyi.symm
    obtain ⟨z, hz, _⟩ := NormalizedHilbert.ChartRecovery.GradedHilbert.normalizedHilbertChart_recovery a b S q (vi ≫ x) yi hi
    exact ⟨z.left, congrArg Over.Hom.left hz⟩)
  apply (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_factorization_iff a S q x).mpr
  let y := OverFactorization.overHomOfFactorization g (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q) x hg
  have hy : y ≫ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q = x := OverFactorization.overHomOfFactorization_comp _ _ _ hg
  exact ⟨y, hy, fun z hz => (cancel_mono (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartRestriction.GradedHilbert
