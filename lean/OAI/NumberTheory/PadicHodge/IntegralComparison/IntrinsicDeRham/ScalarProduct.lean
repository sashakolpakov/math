import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.ScalarWedge
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex

/-! # Scalar Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.ScalarProduct.Intrinsic

noncomputable section

/-! The actual native scalar-form map preserves the integral product
on every geometric open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def unit (M : ModuleCat.{u} R) : M →+ (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).obj M :=
  (TensorProduct.mk R S M (1 : S)).toAddMonoidHom

theorem unit_natural {M N : ModuleCat.{u} R} (a : M ⟶ N) (x : M) :
    (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S).map a (unit R S M x) = unit R S N (a x) :=
  LinearMap.baseChange_tmul a.hom (1 : S) x

variable (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

def targetPairing (a b : ℕ) (U : X.left.Opensᵒᵖ) :
    (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)).X a |>.obj U →ₗ[S]
    (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)).X b |>.obj U →ₗ[S]
    (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.preimage R S X Y f).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)).X (a+b) |>.obj U :=
  IntegralDeRham.CechProduct.sectionPairing S Y a b (op (f ⁻¹ᵁ U.unop))

theorem component_product (a b : ℕ) (U : X.left.Opensᵒᵖ)
    (x : ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).X a).obj U)
    (y : ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).X b).obj U) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.map R S X Y f h).f (a+b)).app U
        (unit R S _ (IntegralDeRham.CechProduct.sectionPairing R X a b U x y)) =
      targetPairing R S X Y f a b U
        (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.map R S X Y f h).f a).app U (unit R S _ x))
        (((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicPresheafScalarComplex.BaseIntrinsicPresheafScalarComplex.map R S X Y f h).f b).app U (unit R S _ y)) := by
  let : Algebra R Γ(X.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U.unop) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U.unop)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U.unop) := AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.baseAlgebra R S X Y f U.unop
  let : Algebra Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceAlgebra R S X Y f U.unop
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U.unop) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) := AlgebraicGeometry.Crystalline.Cohomology.Base.OpenSectionScalarAlgebras.BaseOpenSectionScalarAlgebras.sourceTower R S X Y f U.unop h
  exact IntegralDeRham.ScalarWedge.scalar_one_wedge
    R S Γ(X.left, U.unop) Γ(Y.left, f ⁻¹ᵁ U.unop) a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.ScalarProduct.Intrinsic
