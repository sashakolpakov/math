import Mathlib.AlgebraicGeometry.Gluing

/-! # Test Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TestGluing

noncomputable section

/-! Natural maps on arbitrary affine tests glue to actual morphisms of arbitrary schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

structure AffineTestMapData (X Y : Scheme.{u}) where
  map : ∀ {R : CommRingCat.{u}}, (Spec R ⟶ X) → (Spec R ⟶ Y)
  naturality : ∀ {R A : CommRingCat.{u}}
    (x : Spec R ⟶ X) (a : Spec A ⟶ Spec R), a ≫ map x = map (a ≫ x)

namespace AffineTestMapData

variable {X Y : Scheme.{u}} (D : AffineTestMapData X Y)

def chartMap (i : X.affineOpenCover.I₀) : Spec (X.affineOpenCover.X i) ⟶ Y :=
  D.map (X.affineOpenCover.f i)

theorem chartMap_compatible (i j : X.affineOpenCover.I₀) :
    pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫ D.chartMap i =
      pullback.snd _ _ ≫ D.chartMap j := by
  let C := X.affineOpenCover
  let W := pullback (C.f i) (C.f j)
  apply W.affineOpenCover.openCover.hom_ext
  intro k
  let a := W.affineOpenCover.f k ≫ pullback.fst (C.f i) (C.f j)
  let b := W.affineOpenCover.f k ≫ pullback.snd (C.f i) (C.f j)
  have he : a ≫ C.f i = b ≫ C.f j := by
    change (W.affineOpenCover.f k ≫ pullback.fst (C.f i) (C.f j)) ≫ C.f i =
      (W.affineOpenCover.f k ≫ pullback.snd (C.f i) (C.f j)) ≫ C.f j
    rw [Category.assoc, Category.assoc, pullback.condition]
  change W.affineOpenCover.f k ≫ (pullback.fst (C.f i) (C.f j) ≫ D.map (C.f i)) =
    W.affineOpenCover.f k ≫ (pullback.snd (C.f i) (C.f j) ≫ D.map (C.f j))
  exact (Category.assoc _ _ _).symm.trans
    ((D.naturality (C.f i) a).trans ((congrArg D.map he).trans
      ((D.naturality (C.f j) b).symm.trans (Category.assoc _ _ _))))

def glue : X ⟶ Y := X.affineOpenCover.openCover.glueMorphisms D.chartMap D.chartMap_compatible

theorem glue_chart (i : X.affineOpenCover.I₀) : X.affineOpenCover.f i ≫ D.glue = D.chartMap i :=
  X.affineOpenCover.openCover.ι_glueMorphisms D.chartMap D.chartMap_compatible i

theorem glue_unique (f : X ⟶ Y) (hf : ∀ i : X.affineOpenCover.I₀,
    X.affineOpenCover.f i ≫ f = D.chartMap i) : f = D.glue :=
  X.affineOpenCover.openCover.hom_ext f D.glue (fun i => (hf i).trans (D.glue_chart i).symm)

end AffineTestMapData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TestGluing
