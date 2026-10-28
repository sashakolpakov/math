import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterFiber

/-! # Product Germs -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductGerms

noncomputable section

/-! On an actual affine polynomial product chart, the intrinsic
parameter germ is exactly the localized polynomial X minus its scalar. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductChart

variable {k : Type} [Field k] {Z : Scheme} (f : Z ⟶ Spec (.of k))

theorem chart (U : Z.Opens) (hU : IsAffineOpen U) (x : Spec (.of Γ(Z, U)[X])) (a : k) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    (ProductChart.chart f U hU).stalkMap x
      (Affine.ParameterFiber.germ k (ProductChart.parameter f) (ProductChart.chart f U hU x) a) =
      StructureSheaf.toStalk Γ(Z, U)[X] x (Polynomial.X - Polynomial.C (algebraMap k Γ(Z, U) a)) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let j := ProductChart.chart f U hU
  have hc : Affine.ParameterFiber.germ k (j ≫ ProductChart.parameter f) x a =
      j.stalkMap x (Affine.ParameterFiber.germ k (ProductChart.parameter f) (j x) a) := by
    unfold Affine.ParameterFiber.germ
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  calc
    _ = Affine.ParameterFiber.germ k (j ≫ ProductChart.parameter f) x a := hc.symm
    _ = Affine.ParameterFiber.germ k
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k Γ(Z, U))))) x a :=
      congrArg (fun t => Affine.ParameterFiber.germ k t x a) (ProductChart.chart_parameter f U hU)
    _ = StructureSheaf.toStalk Γ(Z, U)[X] x
        ((Polynomial.mapRingHom (algebraMap k Γ(Z, U))) (Polynomial.X - Polynomial.C a)) :=
      AlgebraicGeometry.stalkMap_toStalk_apply
        (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k Γ(Z, U)))) x _
    _ = _ := congrArg (StructureSheaf.toStalk Γ(Z, U)[X] x) (by simp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ProductGerms
