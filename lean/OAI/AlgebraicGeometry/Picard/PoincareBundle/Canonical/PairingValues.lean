import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.KernelPairing

/-! # Pairing Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.PairingValues

noncomputable section

/-! Explicit evaluation of the constructed canonical bilinear pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (f : A ⟶ B) [IsMonHom f] (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) e = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hi : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)

/-- The bilinear homomorphism evaluates to the actual canonical frame ratio. -/
theorem pairing_apply {T : Over S} (x y : T ⟶ Kernel.Scheme.kernelObject f) :
    KernelPairing.pairing φ P Dh Dv f hf e hv hi hh T x y =
      KernelPairing.value φ P Dh Dv f hf e hv x y := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.PairingValues
