import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupFunctionField
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDifferential

/-! # Chart Algebras -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ChartAlgebras.Construction

noncomputable section

/-! Compatible base-field actions on the actual affine charts of a group morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isScalarTower_chartAlgebra
    {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) (U : Y.left.Opens) (V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f.left ⁻¹ᵁ U) :
    letI := GroupFunctionField.Construction.chartAlgebra Y.hom U hU
    letI := GroupFunctionField.Construction.chartAlgebra X.hom V hV
    letI := (f.left.appLE U V hVU).hom.toAlgebra
    IsScalarTower k Γ(Y.left, U) Γ(X.left, V) := by
  let := GroupFunctionField.Construction.chartAlgebra Y.hom U hU
  let := GroupFunctionField.Construction.chartAlgebra X.hom V hV
  let := (f.left.appLE U V hVU).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  have h : Spec.preimage (hU.fromSpec ≫ Y.hom) ≫ f.left.appLE U V hVU =
      Spec.preimage (hV.fromSpec ≫ X.hom) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
      ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec,
      Category.assoc, f.w]
  exact (congrArg CommRingCat.Hom.hom h).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ChartAlgebras.Construction
