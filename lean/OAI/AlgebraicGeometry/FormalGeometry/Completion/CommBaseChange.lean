import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Comm Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CommBaseChange.Construction

noncomputable section

/-!
# Completion: base change and restriction for commutative algebras

These are the algebra functors needed to descend the finite affine local
representatives. The adjunction is the actual tensor-product universal property.
-/

open _root_.CategoryTheory TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction along the actual ring map. -/
def commAlgRestrict : CommAlgCat.{u} S ⥤ CommAlgCat.{u} R where
  obj A :=
    letI : Algebra R A := Algebra.compHom _ f
    CommAlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom _ f
    letI : Algebra R B := Algebra.compHom _ f
    letI : Algebra R S := f.toAlgebra
    haveI : IsScalarTower R S A := .of_algebraMap_eq' rfl
    haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
    CommAlgCat.ofHom (g.hom.restrictScalars R)

/-- Actual tensor-product base change of commutative algebras. -/
def commAlgExtend : CommAlgCat.{u} R ⥤ CommAlgCat.{u} S := by
  letI : Algebra R S := f.toAlgebra
  exact {
    obj A := CommAlgCat.of S (S ⊗[R] A)
    map {A B} g := CommAlgCat.ofHom
      ((AlgHom.liftEquiv R S A (S ⊗[R] B)) (Algebra.TensorProduct.includeRight.comp g.hom))
    map_id A := by
      apply CommAlgCat.hom_ext
      apply (AlgHom.liftEquiv R S A (S ⊗[R] A)).symm.injective
      ext a
      simp
    map_comp {A B C} g h := by
      apply CommAlgCat.hom_ext
      apply (AlgHom.liftEquiv R S A (S ⊗[R] C)).symm.injective
      ext a
      simp }

/-- The tensor-product adjunction on actual commutative algebras. -/
def commAlgExtendRestrictAdj : commAlgExtend f ⊣ commAlgRestrict f := by
  letI : Algebra R S := f.toAlgebra
  apply Adjunction.mkOfHomEquiv
  refine {
    homEquiv := fun A B => ?_
    homEquiv_naturality_left_symm := ?_
    homEquiv_naturality_right := ?_ }
  · letI : Algebra R B := Algebra.compHom _ f
    haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
    exact {
      toFun g := CommAlgCat.ofHom ((AlgHom.liftEquiv R S A B).symm g.hom)
      invFun g := CommAlgCat.ofHom ((AlgHom.liftEquiv R S A B) g.hom)
      left_inv g := CommAlgCat.hom_ext ((AlgHom.liftEquiv R S A B).apply_symm_apply g.hom)
      right_inv g := CommAlgCat.hom_ext ((AlgHom.liftEquiv R S A B).symm_apply_apply g.hom) }
  · intro A B C g h
    let : Algebra R C := Algebra.compHom _ f
    have : IsScalarTower R S C := .of_algebraMap_eq' rfl
    apply CommAlgCat.hom_ext
    apply (AlgHom.liftEquiv R S A C).symm.injective
    ext a
    simp [commAlgExtend, commAlgRestrict]
  · intro A B C g h
    apply CommAlgCat.hom_ext
    ext a
    rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CommBaseChange.Construction
