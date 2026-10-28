import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePicardFaces
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Cube Product Base -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase

noncomputable section

/-! The three coordinate maps to the group on a product with two
modified factors and the original group as parameter. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.CubeProductCoordinates

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable {B C : Scheme.{u}} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K))

abbrev leftBase := pullback.snd b A.hom
abbrev rightBase := pullback.snd c A.hom
abbrev total := pullback (leftBase A b) (rightBase A c)
abbrev projection : total A b c ⟶ A.left := pullback.fst (leftBase A b) (rightBase A c) ≫ leftBase A b
abbrev ambient : Over (Spec (.of K)) := Over.mk (projection A b c ≫ A.hom)
abbrev leftOver : Over (Spec (.of K)) := Over.mk (leftBase A b ≫ A.hom)
abbrev rightOver : Over (Spec (.of K)) := Over.mk (rightBase A c ≫ A.hom)

def first (u : B ⟶ A.left) (hu : u ≫ A.hom = b) : ambient A b c ⟶ A :=
  Over.homMk (pullback.fst (leftBase A b) (rightBase A c) ≫ pullback.fst b A.hom ≫ u) (by
    change (_ ≫ _ ≫ u) ≫ A.hom = (_ ≫ leftBase A b) ≫ A.hom
    simp only [Category.assoc, hu, pullback.condition]
    exact pullback.condition_assoc (f := leftBase A b) (g := rightBase A c) A.hom)

def second (v : C ⟶ A.left) (hv : v ≫ A.hom = c) : ambient A b c ⟶ A :=
  Over.homMk (pullback.snd (leftBase A b) (rightBase A c) ≫ pullback.fst c A.hom ≫ v) (by
    change (_ ≫ _ ≫ v) ≫ A.hom = (_ ≫ leftBase A b) ≫ A.hom
    simp only [Category.assoc, hv, pullback.condition])

def third : ambient A b c ⟶ A := Over.homMk (projection A b c) rfl

def familyPoint (d : B ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ B) (hs : s ≫ d = 𝟙 _) :
    A.left ⟶ pullback d A.hom :=
  pullback.lift (A.hom ≫ s) (𝟙 _) (by simp [Category.assoc, hs])

omit [GrpObj A] [IsCommMonObj A] in
theorem familyPoint_over (d : B ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ B) (hs : s ≫ d = 𝟙 _) :
    familyPoint A d s hs ≫ pullback.snd d A.hom = 𝟙 _ := pullback.lift_snd _ _ _

def leftAxis (s : Spec (.of K) ⟶ C) (hs : s ≫ c = 𝟙 _) : leftOver A b ⟶ ambient A b c :=
  Over.homMk
    (ProductBaseAxes.Construction.ProductBaseChangeAxes.left (leftBase A b) (rightBase A c)
      (familyPoint A c s hs) (familyPoint_over A c s hs)) (by
    change _ ≫ (projection A b c ≫ A.hom) = leftBase A b ≫ A.hom
    rw [← Category.assoc, ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over])

def rightAxis (s : Spec (.of K) ⟶ B) (hs : s ≫ b = 𝟙 _) : rightOver A c ⟶ ambient A b c :=
  Over.homMk
    (ProductBaseAxes.Construction.ProductBaseChangeAxes.right (leftBase A b) (rightBase A c)
      (familyPoint A b s hs) (familyPoint_over A b s hs)) (by
    change _ ≫ (projection A b c ≫ A.hom) = rightBase A c ≫ A.hom
    rw [← Category.assoc, ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over])

theorem left_second (v : C ⟶ A.left) (hv : v ≫ A.hom = c)
    (s : Spec (.of K) ⟶ C) (hs : s ≫ c = 𝟙 _)
    (hzero : s ≫ v = (MonObj.one (X := A)).left) :
    leftAxis A b c s hs ≫ second A b c v hv = 1 := by
  apply Over.OverMorphism.ext
  change ProductBaseAxes.Construction.ProductBaseChangeAxes.left (leftBase A b) (rightBase A c)
      (familyPoint A c s hs) (familyPoint_over A c s hs) ≫
      pullback.snd (leftBase A b) (rightBase A c) ≫ pullback.fst c A.hom ≫ v =
    (leftBase A b ≫ A.hom) ≫ (MonObj.one (X := A)).left
  simp only [ProductBaseAxes.Construction.ProductBaseChangeAxes.left, pullback.lift_snd_assoc, familyPoint,
    Category.assoc, pullback.lift_fst_assoc, hzero]

theorem right_first (u : B ⟶ A.left) (hu : u ≫ A.hom = b)
    (s : Spec (.of K) ⟶ B) (hs : s ≫ b = 𝟙 _)
    (hzero : s ≫ u = (MonObj.one (X := A)).left) :
    rightAxis A b c s hs ≫ first A b c u hu = 1 := by
  apply Over.OverMorphism.ext
  change ProductBaseAxes.Construction.ProductBaseChangeAxes.right (leftBase A b) (rightBase A c)
      (familyPoint A b s hs) (familyPoint_over A b s hs) ≫
      pullback.fst (leftBase A b) (rightBase A c) ≫ pullback.fst b A.hom ≫ u =
    (rightBase A c ≫ A.hom) ≫ (MonObj.one (X := A)).left
  simp only [ProductBaseAxes.Construction.ProductBaseChangeAxes.right, pullback.lift_fst_assoc, familyPoint,
    Category.assoc, hzero]

end Construction.CubeProductCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase
