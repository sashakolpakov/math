import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineTestMorphisms
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Noetherian Affine Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.NoetherianAffineTests

noncomputable section

/-! Relative morphisms and isomorphisms between locally Noetherian
schemes are reconstructed from natural maps on Noetherian affine
test points, with their original base maps retained. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure RelativeNoetherianAffineTestData {S : Scheme.{u}} (X Y : Over S) where
  app : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Spec R ⟶ S),
    (Over.mk f ⟶ X) → (Over.mk f ⟶ Y)
  naturality : ∀ (R A : CommRingCat.{u}) [IsNoetherianRing R] [IsNoetherianRing A]
    (f : Spec R ⟶ S) (g : Spec A ⟶ S) (a : Over.mk g ⟶ Over.mk f) (x : Over.mk f ⟶ X),
    app A g (a ≫ x) = a ≫ app R f x

namespace RelativeNoetherianAffineTestData
variable {S : Scheme.{u}} {X Y : Over S} (D : RelativeNoetherianAffineTestData X Y)

def underlying : Noetherian.AffineTestMorphisms.NoetherianAffineTestMorphismData X.left Y.left where
  app R _ x := (D.app R (x ≫ X.hom) (Over.homMk x rfl)).left
  naturality R A _ _ a x := by
    let b : Over.mk ((a ≫ x) ≫ X.hom) ⟶ Over.mk (x ≫ X.hom) :=
      Over.homMk a (Category.assoc a x X.hom).symm
    exact congrArg Over.Hom.left
      (D.naturality R A (x ≫ X.hom) ((a ≫ x) ≫ X.hom) b (Over.homMk x rfl))

variable [IsLocallyNoetherian X.left]

def toHom : X ⟶ Y := Over.homMk D.underlying.toHom (by
  apply Noetherian.AffineTestMorphisms.schemeHom_ext_noetherianAffines
  intro R _ x
  rw [← Category.assoc, D.underlying.toHom_on_affine]
  exact (D.app R (x ≫ X.hom) (Over.homMk x rfl)).w)

theorem toHom_on_affine (R : CommRingCat.{u}) [IsNoetherianRing R]
    (f : Spec R ⟶ S) (x : Over.mk f ⟶ X) :
    x ≫ D.toHom = D.app R f x := by
  apply Over.OverMorphism.ext
  have H := D.underlying.toHom_on_affine R x.left
  change x.left ≫ D.underlying.toHom = (D.app R f x).left
  let e : Over.mk (x.left ≫ X.hom) ⟶ Over.mk f :=
    Over.homMk (𝟙 (Spec R)) ((Category.id_comp f).trans x.w.symm)
  have he : e ≫ x = Over.homMk (U := Over.mk (x.left ≫ X.hom)) (V := X) x.left rfl := by
    apply Over.OverMorphism.ext
    exact Category.id_comp x.left
  have hn := D.naturality R R f (x.left ≫ X.hom) e x
  rw [he] at hn
  have hh := congrArg Over.Hom.left hn
  change (D.app R (x.left ≫ X.hom) (Over.homMk (U := Over.mk (x.left ≫ X.hom)) (V := X) x.left rfl)).left =
    𝟙 (Spec R) ≫ (D.app R f x).left at hh
  exact H.trans (hh.trans (Category.id_comp _))

theorem toHom_unique (h : X ⟶ Y)
    (hh : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Spec R ⟶ S)
      (x : Over.mk f ⟶ X), x ≫ h = D.app R f x) : h = D.toHom := by
  apply Over.OverMorphism.ext
  apply D.underlying.toHom_unique
  intro R _ x
  exact congrArg Over.Hom.left (hh R (x ≫ X.hom) (Over.homMk x rfl))

variable [IsLocallyNoetherian Y.left]

def toIso (E : RelativeNoetherianAffineTestData Y X)
    (hDE : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Spec R ⟶ S)
      (x : Over.mk f ⟶ X), E.app R f (D.app R f x) = x)
    (hED : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (f : Spec R ⟶ S)
      (y : Over.mk f ⟶ Y), D.app R f (E.app R f y) = y) : X ≅ Y where
  hom := D.toHom
  inv := E.toHom
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply Noetherian.AffineTestMorphisms.schemeHom_ext_noetherianAffines
    intro R _ x
    let a : Over.mk (x ≫ X.hom) ⟶ X := Over.homMk x rfl
    have H : a ≫ (D.toHom ≫ E.toHom) = a := by
      rw [← Category.assoc, D.toHom_on_affine, E.toHom_on_affine, hDE]
    have h' := congrArg Over.Hom.left H
    exact h'.trans (Category.comp_id _).symm
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply Noetherian.AffineTestMorphisms.schemeHom_ext_noetherianAffines
    intro R _ y
    let a : Over.mk (y ≫ Y.hom) ⟶ Y := Over.homMk y rfl
    have H : a ≫ (E.toHom ≫ D.toHom) = a := by
      rw [← Category.assoc, E.toHom_on_affine, D.toHom_on_affine, hED]
    have h' := congrArg Over.Hom.left H
    exact h'.trans (Category.comp_id _).symm

end RelativeNoetherianAffineTestData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.NoetherianAffineTests
