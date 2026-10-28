import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesFromGlobal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondTransverseFrameUnits

/-! # Global -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global

noncomputable section

/-! A natural kernel-frame system is determined by its actual universal subgroup-product frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (K : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)

/-- The actual universal point of the subgroup product. -/
def universalPoint : Kernel.Scheme.kernelObject f ⊗ X ⟶ A ⊗ X := Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 X

omit [GrpObj A] [IsMonHom f] in
/-- Its actual included kernel coordinate. -/
theorem universalPoint_fst :
    fst (Kernel.Scheme.kernelObject f) X ≫ Kernel.Scheme.kernelInclusion f = universalPoint f ≫ fst A X := by
  simp [universalPoint]

/-- The frame system supplies an actual global frame on the subgroup product. -/
def globalFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ X).left ≅ Line.Fibers.fiber L (universalPoint f) :=
  K.frame (fst (Kernel.Scheme.kernelObject f) X) (universalPoint f) (universalPoint_fst f)

/-- Every original kernel frame is the actual pullback of that single universal frame. -/
theorem globalFrame_natural {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ X)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) :
    Line.Fibers.pullSection L (Kernel.FramesFromGlobal.liftPoint k a) (universalPoint f) a
      (Kernel.FramesFromGlobal.liftPoint_source (Kernel.Scheme.kernelInclusion f) k a ha)
      (globalFrame f L Dh K).hom = (K.frame k a ha).hom :=
  K.natural (Kernel.FramesFromGlobal.liftPoint k a) (fst (Kernel.Scheme.kernelObject f) X) k
    (by simp [Kernel.FramesFromGlobal.liftPoint]) (universalPoint f) a (universalPoint_fst f) ha
    (Kernel.FramesFromGlobal.liftPoint_source (Kernel.Scheme.kernelInclusion f) k a ha)

variable [GrpObj X] (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (ht : Kernel.FramesTransverseTransport.Transverse f K Dv)

include ht

/-- Transverse multiplication fixes the universal frame on the actual zero section of the second factor. -/
theorem globalFrame_zero :
    Line.Fibers.pullSection L (lift (𝟙 (Kernel.Scheme.kernelObject f)) (1 : Kernel.Scheme.kernelObject f ⟶ X)) (universalPoint f)
      (lift (Kernel.Scheme.kernelInclusion f) (1 : Kernel.Scheme.kernelObject f ⟶ X)) (by simp [universalPoint])
      (globalFrame f L Dh K).hom =
        (Dv.unitFrame (lift (Kernel.Scheme.kernelInclusion f) (1 : Kernel.Scheme.kernelObject f ⟶ X)) (by simp)).hom := by
  have hn := K.natural (lift (𝟙 (Kernel.Scheme.kernelObject f)) (1 : Kernel.Scheme.kernelObject f ⟶ X))
    (fst (Kernel.Scheme.kernelObject f) X) (𝟙 (Kernel.Scheme.kernelObject f)) (by simp)
    (universalPoint f) (lift (Kernel.Scheme.kernelInclusion f) (1 : Kernel.Scheme.kernelObject f ⟶ X))
    (universalPoint_fst f) (by simp) (by simp [universalPoint])
  exact hn.trans (congrArg Iso.hom
    (SecondTransverseFrameUnits.horizontal_frame_eq_vertical_unit f L Dh Dv K ht
      (𝟙 (Kernel.Scheme.kernelObject f)) (lift (Kernel.Scheme.kernelInclusion f) (1 : Kernel.Scheme.kernelObject f ⟶ X)) (by simp) (by simp)))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
