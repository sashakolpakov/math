import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluing

noncomputable section

/-! Natural maps on noetherian affine tests glue to actual morphisms on locally noetherian schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affineCoverCoordinateRing_noetherian (X : Scheme.{u}) [IsLocallyNoetherian X]
    (i : X.affineOpenCover.I₀) : IsNoetherianRing (X.affineOpenCover.X i) := by
  have : IsLocallyNoetherian (Spec (X.affineOpenCover.X i)) :=
    isLocallyNoetherian_of_isOpenImmersion (X.affineOpenCover.f i)
  exact isLocallyNoetherian_Spec.mp this

structure NoetherianAffineMapData (X Y : Scheme.{u}) where
  map : ∀ {R : CommRingCat.{u}} [IsNoetherianRing R], (Spec R ⟶ X) → (Spec R ⟶ Y)
  naturality : ∀ {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (x : Spec R ⟶ X) (a : Spec A ⟶ Spec R), a ≫ map x = map (a ≫ x)

namespace NoetherianAffineMapData

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (D : NoetherianAffineMapData X Y)

def chartMap (i : X.affineOpenCover.I₀) : Spec (X.affineOpenCover.X i) ⟶ Y := by
  letI := affineCoverCoordinateRing_noetherian X i
  exact D.map (X.affineOpenCover.f i)

theorem chartMap_compatible (i j : X.affineOpenCover.I₀) :
    pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫ D.chartMap i =
      pullback.snd _ _ ≫ D.chartMap j := by
  let C := X.affineOpenCover
  let W := pullback (C.f i) (C.f j)
  let : IsNoetherianRing (C.X i) := affineCoverCoordinateRing_noetherian X i
  let : IsNoetherianRing (C.X j) := affineCoverCoordinateRing_noetherian X j
  have : IsLocallyNoetherian W :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst (C.f i) (C.f j))
  apply W.affineOpenCover.openCover.hom_ext
  intro k
  let := affineCoverCoordinateRing_noetherian W k
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

end NoetherianAffineMapData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluing
