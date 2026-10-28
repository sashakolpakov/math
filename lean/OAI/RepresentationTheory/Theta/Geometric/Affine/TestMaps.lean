import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Test Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps

noncomputable section

/-! Coordinates of native affine test maps, with exact composition and
constant-point identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem affineAlgHomOverSpecEquiv_comp
    {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C (g.comp f) =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B C g ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  exact Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)

def affineTestMapEquiv (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (R : Type) [CommRing R] [Algebra ℂ R] :
    (Γ(X.left, ⊤) →ₐ[ℂ] R) ≃ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) where
  toFun f := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(X.left, ⊤) R f ≫ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv
  invFun f := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(X.left, ⊤) R).symm (f ≫ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom)
  left_inv f := by simp
  right_inv f := by simp

theorem affineTestMapEquiv_comp (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (f : Γ(X.left, ⊤) →ₐ[ℂ] R) (g : R →ₐ[ℂ] S) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R S g ≫ affineTestMapEquiv X R f =
      affineTestMapEquiv X S (g.comp f) := by
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc, ← affineAlgHomOverSpecEquiv_comp]

theorem affineAlgHomOverSpecEquiv_constant
    {A R : Type} [CommRing A] [CommRing R] [Algebra ℂ A] [Algebra ℂ R]
    (f : A →ₐ[ℂ] ℂ) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A R ((Algebra.ofId ℂ R).comp f) =
      toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((algebraMap ℂ R).comp f.toRingHom)) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A f).left
  rw [AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  exact Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom (algebraMap ℂ R))

theorem affineTestMapEquiv_constant (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    {R : Type} [CommRing R] [Algebra ℂ R] (f : Γ(X.left, ⊤) →ₐ[ℂ] ℂ) :
    affineTestMapEquiv X R ((Algebra.ofId ℂ R).comp f) =
      toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) ≫ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X).symm f := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(X.left, ⊤) R ((Algebra.ofId ℂ R).comp f) ≫
      (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv =
    toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) f ≫ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv)
  rw [affineAlgHomOverSpecEquiv_constant, Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps
