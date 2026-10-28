import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Affine Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

noncomputable section

/-!
The affine-spectrum adjunction over a base ring, expressed as algebra maps
into the actual global sections of a test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A]

abbrev relativeGlobalAlgebra (T : Over (Spec R)) : CommAlgCat R := ((algΓ R).obj T).unop

def relativeAffineScheme : Over (Spec R) := (algSpec R).obj (.op (CommAlgCat.of R A))

def relativeAffinePointEquiv (T : Over (Spec R)) :
    (T ⟶ relativeAffineScheme R A) ≃ (A →ₐ[R] relativeGlobalAlgebra R T) where
  toFun f := (((algΓAlgSpecAdjunction R).homEquiv T (.op (CommAlgCat.of R A))).symm f).unop.hom
  invFun f := (algΓAlgSpecAdjunction R).homEquiv T (.op (CommAlgCat.of R A))
    (CommAlgCat.ofHom f).op
  left_inv f := ((algΓAlgSpecAdjunction R).homEquiv T (.op (CommAlgCat.of R A))).apply_symm_apply f
  right_inv f := congrArg (fun g => g.unop.hom)
    (((algΓAlgSpecAdjunction R).homEquiv T (.op (CommAlgCat.of R A))).symm_apply_apply
      (CommAlgCat.ofHom f).op)

theorem relativeGlobalAlgebra_map {T U : Over (Spec R)} (f : U ⟶ T) (s : relativeGlobalAlgebra R T) :
    ((algΓ R).map f).unop.hom s = f.left.appTop s := rfl

theorem relativeAffinePointEquiv_natural {T U : Over (Spec R)}
    (f : U ⟶ T) (g : T ⟶ relativeAffineScheme R A) :
    relativeAffinePointEquiv R A U (f ≫ g) =
      ((algΓ R).map f).unop.hom.comp (relativeAffinePointEquiv R A T g) :=
  congrArg (fun h => h.unop.hom) ((algΓAlgSpecAdjunction R).homEquiv_naturality_left_symm f g)

theorem relativeAffinePointEquiv_apply {T : Over (Spec R)}
    (f : T ⟶ relativeAffineScheme R A) (x : A) :
    relativeAffinePointEquiv R A T f x =
      f.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x) := rfl

theorem relativeAffinePointEquiv_postcomp
    {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) {T : Over (Spec R)}
    (f : T ⟶ relativeAffineScheme R B) :
    relativeAffinePointEquiv R A T (f ≫ (algSpec R).map (CommAlgCat.ofHom φ).op) =
      (relativeAffinePointEquiv R B T f).comp φ :=
  congrArg (fun h => h.unop.hom)
    ((algΓAlgSpecAdjunction R).homEquiv_naturality_right_symm f (CommAlgCat.ofHom φ).op)

def relativeAffineGlobalEquiv : A ≃ₐ[R] relativeGlobalAlgebra R (relativeAffineScheme R A) where
  __ := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  commutes' r := (relativeAffinePointEquiv R A (relativeAffineScheme R A) (𝟙 _)).commutes r

theorem relativeAffineGlobalEquiv_apply (x : A) :
    relativeAffineGlobalEquiv R A x = (Scheme.ΓSpecIso (CommRingCat.of A)).inv x := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints
