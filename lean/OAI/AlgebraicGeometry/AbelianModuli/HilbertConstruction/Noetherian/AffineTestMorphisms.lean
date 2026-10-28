import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFromAffineTests
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine Test Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineTestMorphisms

noncomputable section

/-! Natural maps on Noetherian affine tests reconstruct morphisms
from any locally Noetherian scheme. No Noetherian hypothesis is
imposed on the target. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure NoetherianAffineTestMorphismData (X Y : Scheme.{u}) where
  app : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R], (Spec R ⟶ X) → (Spec R ⟶ Y)
  naturality : ∀ (R A : CommRingCat.{u}) [IsNoetherianRing R] [IsNoetherianRing A]
    (f : Spec A ⟶ Spec R) (x : Spec R ⟶ X), app A (f ≫ x) = f ≫ app R x

namespace NoetherianAffineTestMorphismData

instance affineCoverRing_noetherian (Z : Scheme.{u}) [IsLocallyNoetherian Z]
    (i : Z.affineOpenCover.I₀) : IsNoetherianRing (Z.affineOpenCover.X i) :=
  isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (Z.affineOpenCover.f i))

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (D : NoetherianAffineTestMorphismData X Y)

theorem affineCover_compatible (i j : X.affineOpenCover.I₀) :
    pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫
        D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i) =
      pullback.snd (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫
        D.app (X.affineOpenCover.X j) (X.affineOpenCover.f j) := by
  let P := pullback (X.affineOpenCover.f i) (X.affineOpenCover.f j)
  have : IsLocallyNoetherian P := isLocallyNoetherian_of_isOpenImmersion
    (pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j))
  apply P.affineOpenCover.openCover.hom_ext
  intro k
  erw [← Category.assoc, ← Category.assoc, ← D.naturality, ← D.naturality]
  congr 1
  rw [Category.assoc, pullback.condition, ← Category.assoc]

def toHom : X ⟶ Y :=
  X.affineOpenCover.openCover.glueMorphisms
    (fun i => D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i)) D.affineCover_compatible

theorem affineCover_toHom (i : X.affineOpenCover.I₀) :
    X.affineOpenCover.f i ≫ D.toHom = D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i) :=
  X.affineOpenCover.openCover.ι_glueMorphisms
    (fun j => D.app (X.affineOpenCover.X j) (X.affineOpenCover.f j))
    D.affineCover_compatible i

theorem toHom_on_affine (R : CommRingCat.{u}) [IsNoetherianRing R] (x : Spec R ⟶ X) :
    x ≫ D.toHom = D.app R x := by
  let C : (Spec R).OpenCover := X.affineOpenCover.openCover.pullback₁ x
  apply C.hom_ext
  intro i
  change X.affineOpenCover.I₀ at i
  let P := pullback x (X.affineOpenCover.f i)
  have : IsLocallyNoetherian P :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst x (X.affineOpenCover.f i))
  apply P.affineOpenCover.openCover.hom_ext
  intro j
  let a := P.affineOpenCover.f j
  change a ≫ (pullback.fst x (X.affineOpenCover.f i) ≫ (x ≫ D.toHom)) =
    a ≫ (pullback.fst x (X.affineOpenCover.f i) ≫ D.app R x)
  calc
    _ = (a ≫ pullback.snd x (X.affineOpenCover.f i)) ≫
        D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i) := by
      rw [← Category.assoc (pullback.fst _ _) x, pullback.condition, Category.assoc,
        D.affineCover_toHom, ← Category.assoc]
    _ = D.app (P.affineOpenCover.X j)
        ((a ≫ pullback.snd x (X.affineOpenCover.f i)) ≫ X.affineOpenCover.f i) :=
      (D.naturality _ _ _ _).symm
    _ = D.app (P.affineOpenCover.X j) ((a ≫ pullback.fst x (X.affineOpenCover.f i)) ≫ x) := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    _ = (a ≫ pullback.fst x (X.affineOpenCover.f i)) ≫ D.app R x := D.naturality _ _ _ _
    _ = _ := Category.assoc _ _ _

theorem toHom_unique (h : X ⟶ Y)
    (hh : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (x : Spec R ⟶ X),
      x ≫ h = D.app R x) : h = D.toHom := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  exact (hh _ _).trans (D.affineCover_toHom i).symm

end NoetherianAffineTestMorphismData

theorem schemeHom_ext_noetherianAffines {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f g : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (x : Spec R ⟶ X), x ≫ f = x ≫ g) : f = g := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  have : IsNoetherianRing (X.affineOpenCover.X i) := NoetherianAffineTestMorphismData.affineCoverRing_noetherian X i
  exact h _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineTestMorphisms
