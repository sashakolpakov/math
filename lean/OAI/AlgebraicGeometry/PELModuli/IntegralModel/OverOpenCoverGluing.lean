import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlas

/-! # Over Open Cover Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverOpenCoverGluing

noncomputable section

/-! Actual relative maps glue uniquely on a source open cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace OverOpenCover
variable {S : Scheme.{0}} (T : Over S) (C : T.left.OpenCover)

def obj (i : C.I₀) : Over S := Over.mk (C.f i ≫ T.hom)
def inclusion (i : C.I₀) : obj T C i ⟶ T := Over.homMk (C.f i) rfl

instance obj_reduced [IsReduced T.left] (i : C.I₀) : IsReduced (obj T C i).left :=
  isReduced_of_isOpenImmersion (C.f i)

def overlap (i j : C.I₀) : Over S := Over.mk ((pullback.fst (C.f i) (C.f j) ≫ C.f i) ≫ T.hom)

def overlapLeft (i j : C.I₀) : overlap T C i j ⟶ obj T C i :=
  Over.homMk (pullback.fst _ _) (Category.assoc _ _ _).symm

def overlapRight (i j : C.I₀) : overlap T C i j ⟶ obj T C j := Over.homMk (pullback.snd _ _) (by
  change pullback.snd (C.f i) (C.f j) ≫ (C.f j ≫ T.hom) = _
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫ T.hom) (pullback.condition (f := C.f i) (g := C.f j)).symm)

theorem overlap_condition (i j : C.I₀) :
    overlapLeft T C i j ≫ inclusion T C i = overlapRight T C i j ≫ inclusion T C j := by
  apply Over.OverMorphism.ext
  exact pullback.condition

instance overlap_reduced [IsReduced T.left] (i j : C.I₀) : IsReduced (overlap T C i j).left := by
  have : IsReduced (C.X i) := isReduced_of_isOpenImmersion (C.f i)
  exact isReduced_of_isOpenImmersion (pullback.fst (C.f i) (C.f j))

theorem hom_ext {Z : Over S} (f g : T ⟶ Z)
    (h : ∀ i, inclusion T C i ≫ f = inclusion T C i ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply C.hom_ext
  intro i
  exact congrArg Over.Hom.left (h i)

theorem existsUnique_glued_morphism {Z : Over S} (f : ∀ i, obj T C i ⟶ Z)
    (h : ∀ i j, overlapLeft T C i j ≫ f i = overlapRight T C i j ≫ f j) :
    ∃! q : T ⟶ Z, ∀ i, inclusion T C i ≫ q = f i := by
  have hm (i j) : pullback.fst (C.f i) (C.f j) ≫ (f i).left =
      pullback.snd (C.f i) (C.f j) ≫ (f j).left := congrArg Over.Hom.left (h i j)
  let q := C.glueMorphisms (fun i => (f i).left) hm
  have hq (i) : C.f i ≫ q = (f i).left := C.ι_glueMorphisms _ hm i
  have hbase : q ≫ Z.hom = T.hom := by
    apply C.hom_ext
    intro i
    rw [← Category.assoc, hq i]
    exact (f i).w
  let a : T ⟶ Z := Over.homMk q hbase
  have ha (i) : inclusion T C i ≫ a = f i := Over.OverMorphism.ext (hq i)
  exact ⟨a, ha, fun b hb => OverOpenCover.hom_ext T C b a (fun i => (hb i).trans (ha i).symm)⟩

end OverOpenCover

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverOpenCoverGluing
