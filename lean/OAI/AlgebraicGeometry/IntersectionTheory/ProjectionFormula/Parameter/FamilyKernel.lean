import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.SectionKernel
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction

/-! # Family Kernel -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyKernel

noncomputable section

/-! Every marked scalar section of an actual determinant-open
product has stalk quotient by the native affine parameter germ. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyChart.Family

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  {Z F : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (t : F ⟶ Spec (.of (Polynomial.MatrixPath.Ring A))) (pr : F ⟶ Z)
  (h : IsPullback t pr (Polynomial.IntegralProduct.parameterBase A) f)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) (s : Z ⟶ F)
  (hs : s ≫ pr = 𝟙 Z)
  (ht : s ≫ t = f ≫ Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A a ha)))

include h hs ht

theorem closed : IsClosedImmersion s := by
  let : IsClosedImmersion (s ≫ FamilyChart.Family.chart A f t pr h) := by
    rw [FamilyChart.Family.section_chart A f t pr h a ha s hs ht]
    infer_instance
  exact IsClosedImmersion.of_comp s (FamilyChart.Family.chart A f t pr h)

theorem kernel (z : Z) : RingHom.ker (s.stalkMap z).hom =
    Ideal.span {Affine.ParameterFiber.germ ℂ (t ≫ Polynomial.IntegralProduct.toLine A) (s z) a} := by
  let j := FamilyChart.Family.chart A f t pr h
  have hc : s ≫ j = (𝟙 Z) ≫ Polynomial.ProductChart.Section.sectionMap f a := by
    rw [Category.id_comp]
    exact FamilyChart.Family.section_chart A f t pr h a ha s hs ht
  have hk := Stalk.KernelSquare.principal_to_chart j
    (Polynomial.ProductChart.Section.sectionMap f a) (𝟙 Z) s hc z
    (fun x => Affine.ParameterFiber.germ ℂ (Polynomial.ProductChart.parameter f) x a)
    (Polynomial.SectionKernel.kernel f a z)
  have hg : j.stalkMap (s z)
      (Affine.ParameterFiber.germ ℂ (Polynomial.ProductChart.parameter f) (j (s z)) a) =
      Affine.ParameterFiber.germ ℂ (t ≫ Polynomial.IntegralProduct.toLine A) (s z) a :=
    (Affine.ParameterRestriction.comp j (Polynomial.ProductChart.parameter f) (s z) a).symm.trans
      (congrArg (fun q => Affine.ParameterFiber.germ ℂ q (s z) a)
        (FamilyChart.Family.chart_parameter A f t pr h))
  exact hk.trans (congrArg (fun r => Ideal.span {r}) hg)

def quotientEquiv (z : Z) :
    (F.presheaf.stalk (s z) ⧸
      Ideal.span {Affine.ParameterFiber.germ ℂ (t ≫ Polynomial.IntegralProduct.toLine A) (s z) a}) ≃+*
        Z.presheaf.stalk z := by
  let : IsClosedImmersion s := closed A f t pr h a ha s hs ht
  exact (Ideal.quotEquivOfEq (kernel A f t pr h a ha s hs ht z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (s.stalkMap_surjective z))

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyKernel
