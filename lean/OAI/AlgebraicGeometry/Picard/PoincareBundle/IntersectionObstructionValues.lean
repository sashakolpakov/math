import OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFrameValues

/-! # Intersection Obstruction Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionObstructionValues

noncomputable section

/-! The global intersection obstruction is exactly the ratio of the two original frames at each pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {S : Scheme.{u}} {H K A B : Over S} (i : H ⟶ A) (j : K ⟶ B)
  (Q : Line.Bundles.LineBundle (A ⊗ B).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ B).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 B).left).obj Q.sheaf)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ K).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ j).left).obj Q.sheaf)

/-- The ratio is preserved by the same actual comparison to the ambient Poincare fiber. -/
theorem value_eq {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    Kernel.IntersectionFrames.obstruction i j Q s t a b = Line.FrameUnits.frameRatio
      (GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 B) Q s (lift a (b ≫ j)) (lift (a ≫ i) (b ≫ j))
        (IntersectionFrameValues.horizontal_pair i j a b))
      (GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ j) Q t (lift (a ≫ i) b) (lift (a ≫ i) (b ≫ j))
        (IntersectionFrameValues.vertical_pair i j a b)) := by
  have hp := FrameRatioPullback.frameRatio_postcomp (FrameRatioPullback.pullFrame (lift a b).left (Kernel.IntersectionFrames.horizontalFrame i j Q s))
    (FrameRatioPullback.pullFrame (lift a b).left (Kernel.IntersectionFrames.verticalFrame i j Q t))
    (Line.Fibers.fiberPullbackIso Q (lift a b) (i ⊗ₘ j) (lift (a ≫ i) (b ≫ j)) (lift_map a b i j))
  exact hp.symm.trans (congrArg₂ Line.FrameUnits.frameRatio (IntersectionFrameValues.horizontal_evaluation i j Q s a b)
    (IntersectionFrameValues.vertical_evaluation i j Q t a b))

/-- Pointwise equality of the actual two frame systems gives precisely the obstruction hypothesis
used in inducing-line descent, with no reduction of the test schemes. -/
theorem trivial_of_point_frames
    (he : ∀ (T : Over S) (a : T ⟶ H) (b : T ⟶ K),
      GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 B) Q s (lift a (b ≫ j)) (lift (a ≫ i) (b ≫ j))
          (IntersectionFrameValues.horizontal_pair i j a b) =
        GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ j) Q t (lift (a ≫ i) b) (lift (a ≫ i) (b ≫ j))
          (IntersectionFrameValues.vertical_pair i j a b)) :
    ∀ (T : Over S) (a : T ⟶ H) (b : T ⟶ K), Kernel.IntersectionFrames.obstruction i j Q s t a b = 1 := by
  intro T a b
  exact (value_eq i j Q s t a b).trans ((Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr (he T a b))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionObstructionValues
