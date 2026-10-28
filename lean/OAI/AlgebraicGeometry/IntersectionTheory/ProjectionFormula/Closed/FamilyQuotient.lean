import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImageStalkModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ScalarKernelModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.AtPoint
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.KernelSquare

/-! # Family Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FamilyQuotient

noncomputable section

/-! In an actual closed-family endpoint square, quotienting the
native family-support module by the parameter gives the native endpoint
support module with its ambient-family scalar action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

variable {V W X Y : Scheme} [IsIntegral V] [IsIntegral W]
  (i : W ⟶ Y) [IsClosedImmersion i] (j : V ⟶ X) [IsClosedImmersion j]
  (u : X ⟶ Y) (v : V ⟶ W) [IsClosedImmersion v]
  (h : j ≫ u = v ≫ i) (t : Y ⟶ Spec (.of ℂ[X])) (a : ℂ) (z : V)
  (hy : u (j z) ∈ (ImmersionSupport.support i : Set Y))
  (hv : RingHom.ker (v.stalkMap z).hom =
    Ideal.span {Affine.ParameterFiber.germ ℂ (i ≫ t) (v z) a})

def equiv :
    QuotSMulTop (Affine.ParameterFiber.germ ℂ t (u (j z)) a)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Y (ImmersionSupport.support i) (u (j z)) hy) ≃ₗ[Y.presheaf.stalk (u (j z))]
        ((ModuleCat.restrictScalars (u.stalkMap (j z)).hom).obj
          (CycleClass.Thom.IntersectionGeometry.localSupportModule X (ImmersionSupport.support j) (j z) (ImageStalkModule.mem j z))) := by
  let R := Y.presheaf.stalk (u (j z))
  let R₀ := X.presheaf.stalk (j z)
  let S := W.presheaf.stalk (v z)
  let T := V.presheaf.stalk z
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X (ImmersionSupport.support j) (j z) (ImageStalkModule.mem j z)
  let r : R := Affine.ParameterFiber.germ ℂ t (u (j z)) a
  have hp : i (v z) = u (j z) := congrArg (fun g : V ⟶ Y => g z) h.symm
  let β := Integral.StalkImage.map i (v z) (u (j z)) hp
  let : Algebra R R₀ := (u.stalkMap (j z)).hom.toAlgebra
  let : Algebra R S := β.hom.toAlgebra
  let : Algebra R₀ T := (j.stalkMap z).hom.toAlgebra
  let : Algebra R T := ((j.stalkMap z).hom.comp (u.stalkMap (j z)).hom).toAlgebra
  let : IsScalarTower R R₀ T := IsScalarTower.of_algebraMap_eq' rfl
  let : Module R N := Module.compHom N (u.stalkMap (j z)).hom
  let : IsScalarTower R R₀ N := IsScalarTower.of_compHom R R₀ N
  let φ : S →ₐ[R] T :=
    { (v.stalkMap z).hom with
      commutes' := fun b => congrArg (fun g : R ⟶ T => g b)
        (Stalk.KernelSquare.square u i v j h z) }
  have hk : RingHom.ker φ.toRingHom = Ideal.span {algebraMap R S r} :=
    hv.trans (congrArg (fun b => Ideal.span {b})
      (Parameter.AtPoint.germ i t (v z) (u (j z)) hp a).symm)
  let eS := ImageStalkModule.moduleEquiv_at i (v z) (u (j z)) hp hy
  let eT := (ImageStalkModule.moduleEquiv j z).restrictScalars R
  exact (QuotSMulTop.congr r eS).trans
    ((ScalarKernelModule.equiv R S T r φ (v.stalkMap_surjective z) hk).trans eT.symm)

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FamilyQuotient
