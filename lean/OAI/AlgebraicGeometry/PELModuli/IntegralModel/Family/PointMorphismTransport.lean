import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison

/-! # Point Morphism Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointMorphismTransport.FamilyPointTransport

noncomputable section

/-! A family morphism compatible with two comparison isomorphisms
commutes with transport of actual points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} (A B : Over S) (m : A ⟶ B) (f g : T ⟶ S)

theorem liftPoint_map (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    PointBaseChange.FamilyPointTransport.liftPoint A f x hx ≫ ((Over.pullback f).map m).left =
      PointBaseChange.FamilyPointTransport.liftPoint B f (x ≫ m.left) (by rw [Category.assoc, m.w]; exact hx) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Cartesian.FamilyMorphismComparison.over_pullback_map_fst, ← Category.assoc, PointBaseChange.FamilyPointTransport.liftPoint_fst, PointBaseChange.FamilyPointTransport.liftPoint_fst]
  · erw [Category.assoc, ((Over.pullback f).map m).w, PointBaseChange.FamilyPointTransport.liftPoint_snd, PointBaseChange.FamilyPointTransport.liftPoint_snd]

theorem transport_map
    (eA : (Over.pullback f).obj A ≅ (Over.pullback g).obj A)
    (eB : (Over.pullback f).obj B ≅ (Over.pullback g).obj B)
    (hm : (Over.pullback f).map m ≫ eB.hom = eA.hom ≫ (Over.pullback g).map m)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    PointBaseChange.FamilyPointTransport.transport A f g eA x hx ≫ m.left =
      PointBaseChange.FamilyPointTransport.transport B f g eB (x ≫ m.left) (by rw [Category.assoc, m.w]; exact hx) := by
  have he := congrArg Over.Hom.left hm
  simp only [Over.comp_left] at he
  change (PointBaseChange.FamilyPointTransport.liftPoint A f x hx ≫ eA.hom.left ≫ pullback.fst A.hom g) ≫ m.left = _
  rw [Category.assoc, Category.assoc, ← Cartesian.FamilyMorphismComparison.over_pullback_map_fst g m,
    ← Category.assoc eA.hom.left, ← he, ← Category.assoc,
    ← Category.assoc (PointBaseChange.FamilyPointTransport.liftPoint A f x hx), liftPoint_map A B m f x hx, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointMorphismTransport.FamilyPointTransport
