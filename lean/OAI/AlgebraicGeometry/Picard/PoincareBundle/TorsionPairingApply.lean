import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing

/-! # Torsion Pairing Apply -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairingApply

noncomputable section

/-! The full torsion pairing evaluates to the actual canonical frame ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing.Poincare

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (n : ℕ)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) σ = Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n))
    (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) σ = Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)

/-- Evaluating the bilinear wrapper retains the two actual canonical kernel frames. -/
theorem value (T : Over S) (a b : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    TorsionPairing.Poincare.torsionPairing φ P Dh Dv n σ hv hp hh T a b =
    ConcreteKernelPairing.Concrete.value ((𝟙 A) ^ n) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n))
      (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
      (Pulled.KernelFrames.Poincare.kernelFrames (φ ^ n) P Dh ((𝟙 A) ^ n) (TorsionPairing.Poincare.torsion_annihilation φ n))
      (CanonicalPoincare.LineDescent.secondKernelFrames (φ ^ n) P Dh Dv ((𝟙 A) ^ n) (TorsionPairing.Poincare.torsion_annihilation φ n) σ hv) a b := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairingApply
