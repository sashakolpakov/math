import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalFrameEvaluation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalVerticalDescentCharacter

/-! # Global Frame Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalFrameProducts

noncomputable section

/-! The actual global frame on the subgroup product is multiplicative for the parameter-family product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B] [GrpObj X]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh)

omit [GrpObj X] in
/-- A common included subgroup coordinate identifies the global fiber frame with the transported original frame. -/
theorem frame_eq {T : Over S} (a : T ⟶ Kernel.Scheme.kernelObject f ⊗ X) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hk : a ≫ fst (Kernel.Scheme.kernelObject f) X = k)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = (a ≫ KernelFrame.Global.universalPoint f) ≫ fst A X) :
    GlobalVerticalDescentCharacter.frame (L.pullback (KernelFrame.Global.universalPoint f).left)
      (KernelFrame.Global.globalFrame f L Dh Kh).symm a =
    Pulled.LineSection.transportFrame (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl
      (Kh.frame k (a ≫ KernelFrame.Global.universalPoint f) ha) := by
  subst k
  have h := GlobalFrameEvaluation.frame_at f L Dh Kh a ha
  apply Iso.ext
  apply (cancel_mono (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl).hom).mp
  change (Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (KernelFrame.Global.globalFrame f L Dh Kh).symm a.left).symm.hom ≫
      (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl).hom =
    ((Kh.frame (a ≫ fst (Kernel.Scheme.kernelObject f) X) (a ≫ KernelFrame.Global.universalPoint f) ha).hom ≫
      (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl).inv) ≫
      (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg Iso.hom h

variable (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (ht : FramesTransverseTransport.Transverse f Kh Dv)

include ht

/-- Transversality of the original kernel frames makes the actual global parameter frame multiplicative. -/
theorem product {T : Over S} (a b c : T ⟶ Kernel.Scheme.kernelObject f ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (snd (Kernel.Scheme.kernelObject f) X) (fst (Kernel.Scheme.kernelObject f) X) a b c) (U : T.left.Opens) :
    ((Vertical.ParameterKernelFrames.multiplication (Kernel.Scheme.kernelInclusion f) L Dv).product a b c h).app U
      ((GlobalVerticalDescentCharacter.frame (L.pullback (KernelFrame.Global.universalPoint f).left)
        (KernelFrame.Global.globalFrame f L Dh Kh).symm a).hom.app U (1 : Γ(T.left, U)))
      ((GlobalVerticalDescentCharacter.frame (L.pullback (KernelFrame.Global.universalPoint f).left)
        (KernelFrame.Global.globalFrame f L Dh Kh).symm b).hom.app U (1 : Γ(T.left, U))) =
    (GlobalVerticalDescentCharacter.frame (L.pullback (KernelFrame.Global.universalPoint f).left)
      (KernelFrame.Global.globalFrame f L Dh Kh).symm c).hom.app U (1 : Γ(T.left, U)) := by
  let k := a ≫ fst (Kernel.Scheme.kernelObject f) X
  have hka : k ≫ Kernel.Scheme.kernelInclusion f = (a ≫ KernelFrame.Global.universalPoint f) ≫ fst A X := by simp [k, KernelFrame.Global.universalPoint]
  have hkb : k ≫ Kernel.Scheme.kernelInclusion f = (b ≫ KernelFrame.Global.universalPoint f) ≫ fst A X := by
    simpa only [k, KernelFrame.Global.universalPoint, Category.assoc, tensorHom_fst] using congrArg (fun z => z ≫ Kernel.Scheme.kernelInclusion f) h.2.1
  have hkc : k ≫ Kernel.Scheme.kernelInclusion f = (c ≫ KernelFrame.Global.universalPoint f) ≫ fst A X := by
    simpa only [k, KernelFrame.Global.universalPoint, Category.assoc, tensorHom_fst] using congrArg (fun z => z ≫ Kernel.Scheme.kernelInclusion f) h.2.2
  rw [Vertical.ParameterProducts.product_eq,
    frame_eq f L Dh Kh a k rfl hka, frame_eq f L Dh Kh b k h.2.1.symm hkb,
    frame_eq f L Dh Kh c k h.2.2.symm hkc]
  exact Bilinear.FrameProducts.product_transport
    (Dv.product _ _ _ (Vertical.ParameterProducts.mapped_relation (Kernel.Scheme.kernelInclusion f) a b c h))
    (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L a (a ≫ KernelFrame.Global.universalPoint f) rfl).symm
    (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L b (b ≫ KernelFrame.Global.universalPoint f) rfl).symm
    (Pulled.LineBilinear.fiberComparison (KernelFrame.Global.universalPoint f) L c (c ≫ KernelFrame.Global.universalPoint f) rfl).symm
    (Kh.frame k (a ≫ KernelFrame.Global.universalPoint f) hka).hom (Kh.frame k (b ≫ KernelFrame.Global.universalPoint f) hkb).hom
    (Kh.frame k (c ≫ KernelFrame.Global.universalPoint f) hkc).hom
    (ht T k _ _ _ hka hkb hkc (Vertical.ParameterProducts.mapped_relation (Kernel.Scheme.kernelInclusion f) a b c h)) U

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.GlobalFrameProducts
