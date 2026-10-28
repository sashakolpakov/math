import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Frames From Global -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesFromGlobal

noncomputable section

/-!
# Canonical natural kernel-point frames from the actual global subgroup trivialization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} {H A X : Over S} (i : H ⟶ A)

/-- Lift a point on the subgroup in the first coordinate while retaining the other actual coordinate. -/
def liftPoint {T : Over S} (k : T ⟶ H) (x : T ⟶ A ⊗ X) : T ⟶ H ⊗ X := lift k (x ≫ snd A X)

/-- The lifted point maps to the original point under the actual subgroup-product inclusion. -/
theorem liftPoint_source {T : Over S} (k : T ⟶ H) (x : T ⟶ A ⊗ X) (hk : k ≫ i = x ≫ fst A X) :
    liftPoint k x ≫ (i ⊗ₘ 𝟙 X) = x := by
  apply CartesianMonoidalCategory.hom_ext
  · dsimp only [liftPoint]
    rw [Category.assoc, tensorHom_fst, lift_fst_assoc]
    exact hk
  · dsimp only [liftPoint]
    rw [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd]

/-- The actual subgroup-coordinate lift is natural on every test scheme. -/
theorem liftPoint_natural {T T' : Over S} (a : T' ⟶ T) (k : T ⟶ H) (x : T ⟶ A ⊗ X)
    (k' : T' ⟶ H) (x' : T' ⟶ A ⊗ X) (hak : a ≫ k = k') (hax : a ≫ x = x') :
    a ≫ liftPoint k x = liftPoint k' x' := by
  dsimp only [liftPoint]
  rw [comp_lift, ← Category.assoc a x (snd A X), hak, hax]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ X).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 X).left).obj L.sheaf)

/-- The frame on each actual subgroup point is constructed from the global trivialization. -/
def frame {T : Over S} (k : T ⟶ H) (x : T ⟶ A ⊗ X) (hk : k ≫ i = x ≫ fst A X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L x :=
  GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 X) L s (liftPoint k x) x (liftPoint_source i k x hk)

/-- The constructed kernel-point frame has the exact normalized geometric section naturality. -/
theorem frame_natural {T T' : Over S} (a : T' ⟶ T) (k : T ⟶ H) (x : T ⟶ A ⊗ X)
    (hk : k ≫ i = x ≫ fst A X) (k' : T' ⟶ H) (x' : T' ⟶ A ⊗ X)
    (hk' : k' ≫ i = x' ≫ fst A X) (hak : a ≫ k = k') (hax : a ≫ x = x') :
    Line.Fibers.pullSection L a x x' hax (frame i L s k x hk).hom = (frame i L s k' x' hk').hom :=
  GlobalFrameNaturality.atPoint_section_natural (i ⊗ₘ 𝟙 X) L s a (liftPoint k x) x
    (liftPoint_source i k x hk) (liftPoint k' x') x' (liftPoint_source i k' x' hk')
    (liftPoint_natural a k x k' x' hak hax) hax

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesFromGlobal
