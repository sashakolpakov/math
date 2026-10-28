import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase

/-! # Cube Product Frames -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames

noncomputable section

/-! Actual frames of the cube bundle on the two product axes and the
fiber at the group identity. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.CubeProductCoordinates

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable {B C : Scheme.{u}} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K))
variable (u : B ⟶ A.left) (hu : u ≫ A.hom = b) (v : C ⟶ A.left) (hv : v ≫ A.hom = c)
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

abbrev cubeBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (CubeProductBase.Construction.CubeProductCoordinates.total A b c) :=
  CubePicardValue.Construction.CubePicardClass.bundle A L (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c)

theorem left_frame (s : Spec (.of K) ⟶ C) (hs : s ≫ c = 𝟙 _)
    (hzero : s ≫ v = (MonObj.one (X := A)).left) :
    Nonempty (((cubeBundle A b c u hu v hv L).pullback (CubeProductBase.Construction.CubeProductCoordinates.leftAxis A b c s hs).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback b A.hom)) :=
  CubePicardFaces.Construction.CubePicardClass.second_face A L (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c)
    (CubeProductBase.Construction.CubeProductCoordinates.leftAxis A b c s hs) (CubeProductBase.Construction.CubeProductCoordinates.left_second A b c v hv s hs hzero)

theorem right_frame (s : Spec (.of K) ⟶ B) (hs : s ≫ b = 𝟙 _)
    (hzero : s ≫ u = (MonObj.one (X := A)).left) :
    Nonempty (((cubeBundle A b c u hu v hv L).pullback (CubeProductBase.Construction.CubeProductCoordinates.rightAxis A b c s hs).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback c A.hom)) :=
  CubePicardFaces.Construction.CubePicardClass.first_face A L (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c)
    (CubeProductBase.Construction.CubeProductCoordinates.rightAxis A b c s hs) (CubeProductBase.Construction.CubeProductCoordinates.right_first A b c u hu s hs hzero)

abbrev origin : Spec (.of K) ⟶ A.left := (MonObj.one (X := A)).left

omit [IsCommMonObj A] in
theorem origin_over : origin A ≫ A.hom = 𝟙 _ := (MonObj.one (X := A)).w

abbrev originFiber : Over (Spec (.of K)) := Over.mk (pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.projection A b c) (origin A))

def originAxis : originFiber A b c ⟶ CubeProductBase.Construction.CubeProductCoordinates.ambient A b c :=
  Over.homMk (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.projection A b c) (origin A)) (by
    change _ ≫ (CubeProductBase.Construction.CubeProductCoordinates.projection A b c ≫ A.hom) = _
    rw [← Category.assoc, pullback.condition, Category.assoc, origin_over, Category.comp_id]
    rfl)

theorem origin_third : originAxis A b c ≫ CubeProductBase.Construction.CubeProductCoordinates.third A b c = 1 := by
  apply Over.OverMorphism.ext
  exact pullback.condition

theorem origin_frame :
    Nonempty (((cubeBundle A b c u hu v hv L).pullback
      (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.projection A b c) (origin A))).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback (CubeProductBase.Construction.CubeProductCoordinates.projection A b c) (origin A))) :=
  CubePicardFaces.Construction.CubePicardClass.third_face A L (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c)
    (originAxis A b c) (origin_third A b c)

end Construction.CubeProductCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames
