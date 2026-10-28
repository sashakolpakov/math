import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Chart
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialSpecialization

/-! # Chart Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartCriterion.GradedHilbert

noncomputable section

/-! The Hilbert-chart predicate expressed directly through the normalized
matrix at each stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u})

theorem normalizedChart_specializedIdeal {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (t : T.left) :
    Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
      (fun j => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom)
        (Chart.GradedHilbert.universalPolynomialGenerators a S j)) N
      (fun j => (Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S j).map _) =
    Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a ((Normalized.AtlasMaps.Grassmannian.chartMatrix a S x).map (T.left.presheaf.Γgerm t).hom) := by
  change Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal
      (fun j => MvPolynomial.map ((T.left.presheaf.Γgerm t).hom.comp x.left.appTop.hom)
        (Normalized.PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S) j)) N _ = _
  rw [Normalized.PolynomialSpecialization.GradedHilbert.normalizedPolynomialIdeal_specialization]
  congr 1
  rw [Normalized.AtlasMaps.Grassmannian.chartMatrix, Normalized.Chart.Grassmannian.normalizedChartRepresentation_apply]
  ext i j
  rfl

theorem normalizedHilbertChart_mem_iff (q : ℕ → ℕ) {T : Over S} (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T) ↔
      ∀ d ∈ BoundedHilbert.DegreeLocus.GradedHilbert.hilbertFlatDegreeSet n (Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)) N, ∀ t : T.left,
        Module.Flat (T.left.presheaf.stalk t)
          (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a
            ((Normalized.AtlasMaps.Grassmannian.chartMatrix a S x).map (T.left.presheaf.Γgerm t).hom)).toIdeal (d + N)) ∧
        Module.finrank (T.left.presheaf.stalk t)
          (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a
            ((Normalized.AtlasMaps.Grassmannian.chartMatrix a S x).map (T.left.presheaf.Γgerm t).hom)).toIdeal (d + N)) + q d =
          Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N)) := by
  rw [Chart.GradedHilbert.normalizedHilbertChartSubfunctor, BoundedHilbert.DegreeLocus.GradedHilbert.boundedHilbertDegreeSubfunctor_mem]
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro _
  change (∀ t, _) ↔ ∀ t, _
  apply forall_congr'
  intro t
  dsimp only [Homogeneous.DegreeLoci.GradedHilbert.degreeQuotientAtStalk]
  rw [normalizedChart_specializedIdeal a S x t]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartCriterion.GradedHilbert
