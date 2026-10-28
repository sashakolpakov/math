import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.Analysis.Complex.Basic

/-! # Affine Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

/-!
# Affine complex points and scheme morphisms

The carrier of affine complex points is the standard algebraic one: complex-algebra
homomorphisms to `ℂ`. Fully faithfulness of mathlib's relative `Spec` functor identifies
these points with scheme morphisms over `Spec ℂ`. No topology is installed here.
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

/-- The complex points of an affine complex algebra are its complex-algebra characters. -/
abbrev affineComplexPoints (A : Type u) [CommRing A] [Algebra ℂ A] := A →ₐ[ℂ] ℂ

/-- The affine scheme of an algebra, equipped with its actual structure morphism. -/
noncomputable abbrev affineSchemeOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))

/-- Packaging an algebra homomorphism as an arrow in the opposite algebra category. -/
def algHomOppositeEquiv (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    (A →ₐ[R] B) ≃ (op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A)) where
  toFun f := (CommAlgCat.ofHom f).op
  invFun f := f.unop.hom
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fully faithful relative spectrum functor, written on ordinary algebra homomorphisms. -/
noncomputable def affineAlgHomOverSpecEquiv (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    (A →ₐ[R] B) ≃ (affineSchemeOver R B ⟶ affineSchemeOver R A) :=
  (algHomOppositeEquiv R A B).trans (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv

/-- The scheme morphism underlying the equivalence is precisely `Spec.map`. -/
@[simp] theorem affineAlgHomOverSpecEquiv_left (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    (affineAlgHomOverSpecEquiv R A B f).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

/-- Complex-algebra characters are exactly morphisms from the complex point over `Spec ℂ`. -/
noncomputable def affineComplexPointsEquiv (A : Type) [CommRing A] [Algebra ℂ A] :
    affineComplexPoints A ≃ (affineSchemeOver ℂ ℂ ⟶ affineSchemeOver ℂ A) :=
  affineAlgHomOverSpecEquiv ℂ A ℂ

/-- This correspondence sends a complex character to its usual spectrum morphism. -/
@[simp] theorem affineComplexPointsEquiv_left (A : Type) [CommRing A] [Algebra ℂ A]
    (x : affineComplexPoints A) :
    (affineComplexPointsEquiv A x).left =
      Spec.map (CommRingCat.ofHom x.toRingHom) := rfl

/-- The base object used for points has identity structure morphism. -/
@[simp] theorem affineComplexBase_hom :
    (affineSchemeOver ℂ ℂ).hom = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
  simp

/-- The spectrum of `ℂ` as a relative affine scheme is the identity object over the base. -/
noncomputable def affineComplexBaseIso :
    affineSchemeOver ℂ ℂ ≅ Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (CommRingCat.of ℂ)) ≫ 𝟙 (Spec (CommRingCat.of ℂ)) =
      (affineSchemeOver ℂ ℂ).hom
    simp)

/-- The standard relative-points formulation, with the literal identity object as source. -/
noncomputable def affineComplexPointsOverEquiv (A : Type) [CommRing A] [Algebra ℂ A] :
    affineComplexPoints A ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ affineSchemeOver ℂ A) :=
  (affineComplexPointsEquiv A).trans
    { toFun := fun f => affineComplexBaseIso.inv ≫ f
      invFun := fun f => affineComplexBaseIso.hom ≫ f
      left_inv := fun f => by simp
      right_inv := fun f => by simp }

/-- The relative-points equivalence has the usual underlying spectrum map. -/
@[simp] theorem affineComplexPointsOverEquiv_left (A : Type) [CommRing A] [Algebra ℂ A]
    (x : affineComplexPoints A) :
    (affineComplexPointsOverEquiv A x).left =
      Spec.map (CommRingCat.ofHom x.toRingHom) := by
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom x.toRingHom) = _
  simp

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
