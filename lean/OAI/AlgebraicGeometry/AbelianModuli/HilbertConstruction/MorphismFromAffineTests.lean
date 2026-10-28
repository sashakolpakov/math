import Mathlib.AlgebraicGeometry.Gluing

/-! # Morphism From Affine Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFromAffineTests

noncomputable section

/-! A natural assignment on all affine test schemes determines an
actual scheme morphism. The construction glues on an affine cover
and proves the formula on every affine test, not only on that cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

structure AffineTestMorphismData (X Y : Scheme.{u}) where
  app : ∀ R : CommRingCat.{u}, (Spec R ⟶ X) → (Spec R ⟶ Y)
  naturality : ∀ (R A : CommRingCat.{u}) (f : Spec A ⟶ Spec R) (x : Spec R ⟶ X),
    app A (f ≫ x) = f ≫ app R x

namespace AffineTestMorphismData
variable {X Y : Scheme.{u}} (D : AffineTestMorphismData X Y)

theorem affineCover_compatible (i j : X.affineOpenCover.I₀) :
    pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫
        D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i) =
      pullback.snd (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫
        D.app (X.affineOpenCover.X j) (X.affineOpenCover.f j) := by
  let P := pullback (X.affineOpenCover.f i) (X.affineOpenCover.f j)
  apply P.affineOpenCover.openCover.hom_ext
  intro k
  erw [← Category.assoc, ← Category.assoc, ← D.naturality, ← D.naturality]
  congr 1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => P.affineOpenCover.openCover.f k ≫ q) pullback.condition).trans
      (Category.assoc _ _ _).symm)

def toHom : X ⟶ Y :=
  X.affineOpenCover.openCover.glueMorphisms
    (fun i => D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i)) D.affineCover_compatible

theorem affineCover_toHom (i : X.affineOpenCover.I₀) :
    X.affineOpenCover.f i ≫ D.toHom =
      D.app (X.affineOpenCover.X i) (X.affineOpenCover.f i) :=
  X.affineOpenCover.openCover.ι_glueMorphisms _ _ i

theorem toHom_on_affine (R : CommRingCat.{u}) (x : Spec R ⟶ X) :
    x ≫ D.toHom = D.app R x := by
  let C : (Spec R).OpenCover := X.affineOpenCover.openCover.pullback₁ x
  apply C.hom_ext
  intro i
  change X.affineOpenCover.I₀ at i
  let P := pullback x (X.affineOpenCover.f i)
  change pullback.fst x (X.affineOpenCover.f i) ≫ (x ≫ D.toHom) =
    pullback.fst x (X.affineOpenCover.f i) ≫ D.app R x
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
    (hh : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ X), x ≫ h = D.app R x) : h = D.toHom := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  exact (hh _ _).trans (D.affineCover_toHom i).symm

end AffineTestMorphismData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismFromAffineTests
