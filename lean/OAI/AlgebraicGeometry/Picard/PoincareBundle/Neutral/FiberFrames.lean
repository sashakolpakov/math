import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

/-! # Fiber Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberFrames

noncomputable section

/-!
# A genuine neutral-axis frame gives natural units on every neutral test fiber
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme

variable {S : Scheme.{u}} {A X : Over S} [GrpObj A]

/-- A neutral test point lifts through the actual neutral axis by its second coordinate. -/
theorem neutral_lift {T : Over S} (a : T ⟶ A ⊗ X) (ha : a ≫ fst A X = 1) :
    (a ≫ snd A X) ≫ ParameterScheme.point A X = a := by
  rw [ParameterScheme.point_comp]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    exact ha.symm
  · rw [lift_snd]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ≅ (Scheme.Modules.pullback (ParameterScheme.point A X).left).obj L.sheaf)

/-- The global neutral-axis frame gives an actual normalized unit frame at each neutral test point. -/
def frame {T : Over S} (a : T ⟶ A ⊗ X) (ha : a ≫ fst A X = 1) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a :=
  GlobalPullbackFrame.atPoint (ParameterScheme.point A X) L s (a ≫ snd A X) a (neutral_lift a ha)

/-- These actual neutral frames commute with every change of test scheme. -/
theorem frame_natural {T U : Over S} (t : U ⟶ T) (a : T ⟶ A ⊗ X) (a' : U ⟶ A ⊗ X)
    (ha : a ≫ fst A X = 1) (ha' : a' ≫ fst A X = 1) (hta : t ≫ a = a') :
    Line.Fibers.pullSection L t a a' hta (frame L s a ha).hom = (frame L s a' ha').hom :=
  GlobalFrameNaturality.atPoint_section_natural (ParameterScheme.point A X) L s t (a ≫ snd A X) a (neutral_lift a ha)
    (a' ≫ snd A X) a' (neutral_lift a' ha')
    ((Category.assoc t a (snd A X)).symm.trans (congrArg (fun b => b ≫ snd A X) hta)) hta

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberFrames
