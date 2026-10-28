import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

/-! # Natural Origin Line Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalOriginLineFrames

noncomputable section

/-! An actual frame at the group identity gives compatible origin-line frames on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (L : Line.Bundles.LineBundle A.left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over S)).left ≅ Line.Fibers.fiber L η[A])

/-- Pull the actual identity frame along the test scheme's structure map. -/
def frame (T : Over S) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L (1 : T ⟶ A) :=
  GlobalPullbackFrame.atPoint η[A] L s (toUnit T) (1 : T ⟶ A) rfl

/-- These origin frames respect every morphism of test schemes. -/
theorem natural {T U : Over S} (a : U ⟶ T) :
    FrameRatioPullback.pullFrame a.left (frame L s T) ≪≫ Line.Fibers.fiberPullbackIso L a (1 : T ⟶ A) (1 : U ⟶ A) (MonObj.comp_one a) =
      frame L s U := by
  have ht : a ≫ toUnit T = toUnit U := Subsingleton.elim _ _
  exact GlobalFrameNaturality.atPoint_pullback η[A] L s a (toUnit T) (1 : T ⟶ A) rfl
    (toUnit U) (1 : U ⟶ A) rfl ht (MonObj.comp_one a)

/-- The corresponding actual structure-sheaf maps have the full fiber-section naturality law. -/
theorem section_natural {T U : Over S} (a : U ⟶ T) :
    Line.Fibers.pullSection L a (1 : T ⟶ A) (1 : U ⟶ A) (MonObj.comp_one a) (frame L s T).hom =
      (frame L s U).hom :=
  congrArg Iso.hom (natural L s a)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalOriginLineFrames
