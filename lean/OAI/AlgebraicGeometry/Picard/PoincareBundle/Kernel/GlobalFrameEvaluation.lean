import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars

/-! # Global Frame Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalFrameEvaluation

noncomputable section

/-! The native global trivialization on the full subgroup product evaluates to the original kernel frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global

/-- The native pulled trivialization and PoincareBundle's pulled frame are the same actual isomorphism. -/
theorem pulledFrame_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ M) :
    (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame s.symm f).symm = FrameRatioPullback.pullFrame f s := by
  apply Iso.ext
  rfl

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)

/-- The global subgroup-product frame recovers the original first-kernel frame at every actual test point. -/
theorem frame_at {T : Over S} (a : T ⟶ Kernel.Scheme.kernelObject f ⊗ X)
    (ha : (a ≫ fst (Kernel.Scheme.kernelObject f) X) ≫ Kernel.Scheme.kernelInclusion f = (a ≫ KernelFrame.Global.universalPoint f) ≫ fst A X) :
    (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (KernelFrame.Global.globalFrame f L Dh Kh).symm a.left).symm ≪≫
      Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl =
    Kh.frame (a ≫ fst (Kernel.Scheme.kernelObject f) X) (a ≫ KernelFrame.Global.universalPoint f) ha := by
  have h := Kh.natural a (fst (Kernel.Scheme.kernelObject f) X) (a ≫ fst (Kernel.Scheme.kernelObject f) X) rfl
    (KernelFrame.Global.universalPoint f) (a ≫ KernelFrame.Global.universalPoint f) (KernelFrame.Global.universalPoint_fst f) ha rfl
  apply Iso.ext
  rw [pulledFrame_eq]
  have hc := GlobalPullbackFrame.comparison_eq (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl
  change (FrameRatioPullback.pullFrame a.left (KernelFrame.Global.globalFrame f L Dh Kh)).hom ≫
    (GlobalPullbackFrame.comparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl).hom = _
  rw [hc]
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalFrameEvaluation
