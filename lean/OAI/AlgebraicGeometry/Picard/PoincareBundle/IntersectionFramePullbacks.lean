import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

/-! # Intersection Frame Pullbacks -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFramePullbacks

noncomputable section

/-! The two canonical kernel-intersection frames are actual global-frame evaluations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {S : Scheme.{u}} {H K A B : Over S} (i : H ⟶ A) (j : K ⟶ B)
  (L : Line.Bundles.LineBundle (A ⊗ B).left)

theorem horizontal_eq (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ B).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 B).left).obj L.sheaf) :
    Kernel.IntersectionFrames.horizontalFrame i j L s = GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 B) L s (𝟙 H ⊗ₘ j) (i ⊗ₘ j)
      (Kernel.IntersectionFrames.horizontal_factor i j) := by
  simp only [Kernel.IntersectionFrames.horizontalFrame, GlobalPullbackFrame.atPoint,
    GlobalPullbackFrame.comparison_eq, FrameRatioPullback.pullFrame, NatIso.trans_app]
  exact (Iso.trans_assoc _ _ _).symm

theorem vertical_eq (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ K).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ j).left).obj L.sheaf) :
    Kernel.IntersectionFrames.verticalFrame i j L s = GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ j) L s (i ⊗ₘ 𝟙 K) (i ⊗ₘ j)
      (Kernel.IntersectionFrames.vertical_factor i j) := by
  simp only [Kernel.IntersectionFrames.verticalFrame, GlobalPullbackFrame.atPoint,
    GlobalPullbackFrame.comparison_eq, FrameRatioPullback.pullFrame, NatIso.trans_app]
  exact (Iso.trans_assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFramePullbacks
