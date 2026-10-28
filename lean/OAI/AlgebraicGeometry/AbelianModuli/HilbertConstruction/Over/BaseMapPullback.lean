import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base Map Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapPullback

noncomputable section

/-! A map of parameter schemes canonically identifies iterated family pullback with pullback along the test scheme's structure map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overBaseMapPullbackIso {S : Scheme.{u}} {T M : Over S} (c : T ⟶ M) (A : Over S) :
    (Over.pullback T.hom).obj A ≅ (Over.pullback c.left).obj ((Over.pullback M.hom).obj A) :=
  eqToIso (congrArg (fun f : T.left ⟶ S => (Over.pullback f).obj A) c.w.symm) ≪≫
    (Over.pullbackComp c.left M.hom).app A

def overBaseMapPullbackMorphism {S : Scheme.{u}} {T M A B : Over S} (c : T ⟶ M)
    (h : (Over.pullback c.left).obj ((Over.pullback M.hom).obj A) ⟶
      (Over.pullback c.left).obj ((Over.pullback M.hom).obj B)) :
    (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B :=
  (overBaseMapPullbackIso c A).hom ≫ h ≫ (overBaseMapPullbackIso c B).inv

theorem overBaseMapPullbackMorphism_isIso_iff {S : Scheme.{u}} {T M A B : Over S} (c : T ⟶ M)
    (h : (Over.pullback c.left).obj ((Over.pullback M.hom).obj A) ⟶
      (Over.pullback c.left).obj ((Over.pullback M.hom).obj B)) :
    IsIso (overBaseMapPullbackMorphism c h) ↔ IsIso h := by
  simp only [overBaseMapPullbackMorphism, isIso_comp_left_iff, isIso_comp_right_iff]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapPullback
