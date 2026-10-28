import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductChart

/-! # Family Chart -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyChart

noncomputable section

/-! Any actual determinant-open parameter product embeds openly
in the full affine-line product, preserving its marked sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  {Z F : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (t : F ⟶ Spec (.of (ProjectionFormula.Polynomial.MatrixPath.Ring A))) (pr : F ⟶ Z)
  (h : IsPullback t pr (Parameter.Polynomial.IntegralProduct.parameterBase A) f)

def chart : F ⟶ ProjectionFormula.Polynomial.ProductChart.space f :=
  h.isoPullback.hom ≫ Parameter.Polynomial.IntegralProduct.inclusion A f

instance chart_open : IsOpenImmersion (chart A f t pr h) := by
  unfold chart
  infer_instance

theorem chart_parameter : chart A f t pr h ≫ ProjectionFormula.Polynomial.ProductChart.parameter f =
    t ≫ Parameter.Polynomial.IntegralProduct.toLine A := by
  change (h.isoPullback.hom ≫ Parameter.Polynomial.IntegralProduct.inclusion A f) ≫
    pullback.fst Parameter.Polynomial.Line.base f = _
  rw [Category.assoc,
    Parameter.Polynomial.IntegralProduct.inclusion, pullback.lift_fst, ← Category.assoc]
  exact congrArg (fun g => g ≫ Parameter.Polynomial.IntegralProduct.toLine A) h.isoPullback_hom_fst

theorem chart_source : chart A f t pr h ≫ ProjectionFormula.Polynomial.ProductChart.source f = pr := by
  change (h.isoPullback.hom ≫ Parameter.Polynomial.IntegralProduct.inclusion A f) ≫
    pullback.snd Parameter.Polynomial.Line.base f = _
  rw [Category.assoc,
    Parameter.Polynomial.IntegralProduct.inclusion, pullback.lift_snd, Category.comp_id]
  exact h.isoPullback_hom_snd

theorem evaluation_toLine (a : ℂ) (ha : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A a ha)) ≫ Parameter.Polynomial.IntegralProduct.toLine A =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) := by
  rw [Parameter.Polynomial.IntegralProduct.toLine, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact ProjectionFormula.Polynomial.MatrixPath.evaluation_algebraMap A a ha p

theorem section_chart (a : ℂ) (ha : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval a ≠ 0) (s : Z ⟶ F)
    (hs : s ≫ pr = 𝟙 Z)
    (ht : s ≫ t = f ≫ Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A a ha))) :
    s ≫ chart A f t pr h = ProjectionFormula.Polynomial.ProductChart.Section.sectionMap f a := by
  apply pullback.hom_ext
  · change (_ ≫ chart A f t pr h) ≫ ProjectionFormula.Polynomial.ProductChart.parameter f =
      ProjectionFormula.Polynomial.ProductChart.Section.sectionMap f a ≫ ProjectionFormula.Polynomial.ProductChart.parameter f
    rw [Category.assoc, chart_parameter, ← Category.assoc, ht, Category.assoc,
      evaluation_toLine, ProjectionFormula.Polynomial.ProductChart.Section.section_parameter]
  · change (_ ≫ chart A f t pr h) ≫ ProjectionFormula.Polynomial.ProductChart.source f =
      ProjectionFormula.Polynomial.ProductChart.Section.sectionMap f a ≫ ProjectionFormula.Polynomial.ProductChart.source f
    rw [Category.assoc, chart_source, hs, ProjectionFormula.Polynomial.ProductChart.Section.section_source]

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyChart
