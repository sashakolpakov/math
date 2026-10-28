import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartCriterion

/-! # Overlap Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OverlapCriterion.GradedHilbert

noncomputable section

/-! The bounded Hilbert conditions agree under the actual Grassmannian
overlap isomorphisms, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u})

theorem normalizedOverlap_polynomialIdeal {T : Over S} (f : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S) :
    Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.AtlasMaps.Grassmannian.chartMatrix a S (f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)) =
      Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b (Normalized.AtlasMaps.Grassmannian.chartMatrix b S
        (f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S)) := by
  have he := Normalized.AtlasMaps.Grassmannian.overlapTransition_matrix a b S f
  rw [Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix] at he
  rw [← Category.assoc, he]
  apply Normalized.PolynomialTransitions.GradedHilbert.normalizedPolynomialIdeal_transition a b _ (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S _)
  exact Normalized.AtlasMaps.Grassmannian.overlapMatrix_unit a b S f

theorem normalizedOverlap_stalkPolynomialIdeal {T : Over S}
    (f : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S) (t : T.left) :
    Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a
      ((Normalized.AtlasMaps.Grassmannian.chartMatrix a S (f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)).map (T.left.presheaf.Γgerm t).hom) =
    Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b ((Normalized.AtlasMaps.Grassmannian.chartMatrix b S
      (f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S)).map
        (T.left.presheaf.Γgerm t).hom) := by
  let : Algebra Γ(T.left, ⊤) (T.left.presheaf.stalk t) := (T.left.presheaf.Γgerm t).hom.toAlgebra
  have he := congrArg (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T.left.presheaf.stalk t))
    (normalizedOverlap_polynomialIdeal a b S f)
  rw [Normalized.PolynomialTransitions.GradedHilbert.normalizedPolynomialIdeal_baseChange, Normalized.PolynomialTransitions.GradedHilbert.normalizedPolynomialIdeal_baseChange] at he
  exact he

theorem normalizedHilbertChart_overlap_mem_iff (q : ℕ → ℕ) {T : Over S}
    (f : T ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S) :
    f ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op T) ↔
      f ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S ∈
        (Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).obj (.op T) := by
  rw [ChartCriterion.GradedHilbert.normalizedHilbertChart_mem_iff, ChartCriterion.GradedHilbert.normalizedHilbertChart_mem_iff]
  apply forall_congr'
  intro d
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro t
  rw [normalizedOverlap_stalkPolynomialIdeal a b S f t]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OverlapCriterion.GradedHilbert
