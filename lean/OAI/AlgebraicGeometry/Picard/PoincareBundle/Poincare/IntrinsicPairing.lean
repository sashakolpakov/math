import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ParameterRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.KernelPairingCharacter

/-! # Intrinsic Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.IntrinsicPairing.Intrinsic

noncomputable section

/-! The actual original Poincare family has the native scalar-cover character given by the inverse canonical kernel pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

variable {k : Type u} [Field k] {A B Z : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj B] [GrpObj Z] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (n : ℕ) [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A) ^ n)).left]
  (f : A ⟶ B) [IsMonHom f]
  (Kh : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) (FirstBiextensionFactor.familyLine P (φ ^ n)) f (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh))
  (J : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (FirstBiextensionFactor.familyLine P (φ ^ n)) ((𝟙 A) ^ n) (TransverseFrames.sourceVertical (φ ^ n) P Dv))
  (hKh : Kernel.FramesTransverseTransport.Transverse f Kh (TransverseFrames.sourceVertical (φ ^ n) P Dv))
  (hJ : Kernel.FramesTransverseTransport.Transverse ((𝟙 A) ^ n) J (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh))

include hp hKh hJ

/-- An actual frame of the pulled original family realizes the inverse kernel pairing as its native character. -/
theorem exists_frame_character :
    ∃ e : (Scheme.Modules.pullback (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n).left).obj
        ((Scheme.Modules.pullback (KernelFrame.Global.universalPoint (X := A) f).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf) ≅
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ A).left,
      ∀ (T : Over (Spec (.of k))) (a : T ⟶ Kernel.Scheme.kernelObject f) (b : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n))
        (z w : T ⟶ A) (_h : (b ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) * z = w)
        (q : T ⟶ Kernel.Scheme.kernelObject f ⊗ A)
        (hz : lift a z ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n) = q)
        (hw : lift a w ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n) = q),
        Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
          (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n).left
            ((Scheme.Modules.pullback (KernelFrame.Global.universalPoint (X := A) f).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf)) e
          q.left (lift a z).left (lift a w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
          (ConcreteKernelPairing.Concrete.value f ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n))
            (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (TransverseFrames.sourceVertical (φ ^ n) P Dv) Kh J a b)⁻¹.val := by
  obtain ⟨r⟩ := Scalar.ParameterRecovery.exists_recovery φ P Dh Dv hp n J hJ (Kernel.Scheme.kernelInclusion f)
  let M := (FirstBiextensionFactor.familyLine P φ).pullback (KernelFrame.Global.universalPoint (X := A) f).left
  refine ⟨Recovered.KernelPairingCharacter.frame f ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (TransverseFrames.sourceVertical (φ ^ n) P Dv) Kh J M r, ?_⟩
  intro T a b z w h q hz hw
  exact Recovered.KernelPairingCharacter.scalar_translation f ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (TransverseFrames.sourceVertical (φ ^ n) P Dv) Kh J M r hKh a b z w h q hz hw

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.IntrinsicPairing.Intrinsic
