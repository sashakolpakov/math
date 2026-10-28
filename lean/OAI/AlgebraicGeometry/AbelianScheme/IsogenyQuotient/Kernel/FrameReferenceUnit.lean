import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberProductOrigin

/-! # Frame Reference Unit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.FrameReferenceUnit.Construction

noncomputable section

/-! A canonical PoincareBundle kernel frame recovers the original multiplication's
unit frame through its actual family-line fiber comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

set_option backward.isDefEq.respectTransparency false in
theorem kernelFrame_to_originalUnit {S : Scheme.{u}} {A B Z X T : Over S}
    [GrpObj A] [GrpObj B] [GrpObj Z] (φ : A ⟶ Z) [IsMonHom φ]
    (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ X).left) (D : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z X) (snd Z X) P)
    (f : A ⟶ B) [IsMonHom f] (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ φ = 1)
    (z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) (a : T ⟶ A ⊗ X) (ha : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = a ≫ fst A X)
    (hu : (a ≫ (φ ⊗ₘ 𝟙 X)) ≫ fst Z X = 1) :
    (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.kernelFrames φ P D f hf).frame z a ha ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso P a (φ ⊗ₘ 𝟙 X) (a ≫ (φ ⊗ₘ 𝟙 X)) rfl = D.unitFrame (a ≫ (φ ⊗ₘ 𝟙 X)) hu := by
  change (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.imageMultiplication φ P D).unitFrame a _ ≪≫ Picard.PoincareBundle.Line.Fibers.fiberPullbackIso P a (φ ⊗ₘ 𝟙 X) (a ≫ (φ ⊗ₘ 𝟙 X)) rfl = _
  rw [Picard.PoincareBundle.Pulled.KernelFrames.Poincare.imageMultiplication, SymmetricMultiplicationUnits.Construction.multiplication_congrCoordinates_unitFrame]
  change (D.unitFrame (a ≫ (φ ⊗ₘ 𝟙 X)) hu ≪≫
      (Picard.PoincareBundle.GlobalPullbackFrame.comparison (φ ⊗ₘ 𝟙 X) P a (a ≫ (φ ⊗ₘ 𝟙 X)) rfl).symm) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso P a (φ ⊗ₘ 𝟙 X) (a ≫ (φ ⊗ₘ 𝟙 X)) rfl = _
  rw [FiberProductOrigin.Construction.fiberPullbackIso_eq_comparison]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.FrameReferenceUnit.Construction
