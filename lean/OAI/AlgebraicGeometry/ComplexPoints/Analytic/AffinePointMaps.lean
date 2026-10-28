import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Topology.Category.TopCat.Basic

/-! # Affine Point Maps -/

namespace OAI.AlgebraicGeometry

/-!+# Continuous maps of affine complex points

The evaluation topology on `affineComplexPoints A = (A →ₐ[ℂ] ℂ)` makes
precomposition by an actual complex algebra homomorphism continuous. These maps
form a contravariant functor from complex commutative algebras to topological
spaces. No continuity assumption on the algebra homomorphism is needed.
-/

universe u v w

section

variable {A : Type u} {B : Type v} {D : Type w}
variable [CommRing A] [Algebra ℂ A]
variable [CommRing B] [Algebra ℂ B]
variable [CommRing D] [Algebra ℂ D]

/-- The continuous map of complex points induced contravariantly by an algebra map. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (f : A →ₐ[ℂ] B) : C(Foundations.Scheme.AffineComplexPoints.affineComplexPoints B, Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) where
  toFun x := x.comp f
  continuous_toFun := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
    intro a
    exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (f a)

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_apply (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x a = x (f a) := rfl

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_id :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (AlgHom.id ℂ A) = ContinuousMap.id (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  ext x a
  rfl

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap_comp (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] D) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (g.comp f) = (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f).comp (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap g) := by
  ext x a
  rfl

/-- Isomorphic complex algebras have homeomorphic spaces of complex points. -/
noncomputable def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph (e : A ≃ₐ[ℂ] B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints B ≃ₜ Foundations.Scheme.AffineComplexPoints.affineComplexPoints A where
  toFun := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.toAlgHom
  invFun := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.symm.toAlgHom
  left_inv x := by
    ext b
    change x (e (e.symm b)) = x b
    exact congrArg x (e.apply_symm_apply b)
  right_inv x := by
    ext a
    change x (e.symm (e a)) = x a
    exact congrArg x (e.symm_apply_apply a)
  continuous_toFun := (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.toAlgHom).continuous
  continuous_invFun := (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap e.symm.toAlgHom).continuous

@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph_apply (e : A ≃ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph e x a = x (e a) := rfl

end

open _root_.CategoryTheory Opposite

/-- Under the standard affine-scheme correspondence, precomposition is composition
with the induced morphism of affine schemes over `Spec ℂ`. -/
@[simp]
theorem ComplexPoints.Analytic.AffinePointMaps.affineComplexPointsEquiv_comap {A B : Type}
    [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv A (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv B x ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B f := by
  apply Over.OverMorphism.ext
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv_left, Over.comp_left, Foundations.Scheme.AffineComplexPoints.affineComplexPointsEquiv_left,
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left]
  exact AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom f.toRingHom)
    (CommRingCat.ofHom x.toRingHom)

/-- Complex points, with their evaluation topology, form a contravariant functor. -/
noncomputable def ComplexPoints.Analytic.AffinePointMaps.affineComplexPointsFunctor : (CommAlgCat.{u} ℂ)ᵒᵖ ⥤ TopCat.{u} where
  obj A := TopCat.of (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A.unop)
  map f := TopCat.ofHom (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f.unop.hom)
  map_id A := by
    ext x a
    rfl
  map_comp f g := by
    ext x a
    rfl

end OAI.AlgebraicGeometry
