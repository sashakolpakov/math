import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.DescentRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterLineRecovery

/-! # Parameter Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ParameterRecovery

noncomputable section

/-! The original Poincare line recovers the multiple-family descent over every parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {k : Type u} [Field k] {A Z : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj Z] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (n : ℕ) [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A) ^ n)).left]
  (J : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (FirstBiextensionFactor.familyLine P (φ ^ n)) ((𝟙 A) ^ n) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv))
  (hJ : Kernel.FramesTransverseTransport.Transverse ((𝟙 A) ^ n) J (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh))
  {K : Over (Spec (.of k))} (t : K ⟶ A)

include hp hJ

/-- Actual scalar-family recovery holds over arbitrary, possibly nonreduced, parameter schemes. -/
theorem exists_recovery :
    Nonempty (Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks)
      (f := fun (_ : PUnit.{1}) => (𝟙 K ⊗ₘ (𝟙 A) ^ n).left)
        ((Scheme.Modules.pullback (t ⊗ₘ 𝟙 A).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf) ≅
      Vertical.KernelDescent.ordinaryDatum ((𝟙 A) ^ n) ((FirstBiextensionFactor.familyLine P (φ ^ n)).pullback (t ⊗ₘ 𝟙 A).left)
        (Vertical.ParameterKernelFrames.multiplication t (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv))
        (Vertical.ParameterKernelFrames.frames t ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) J)) := by
  obtain ⟨r⟩ := DescentRecovery.exists_recovery φ P Dh Dv hp n J hJ
  exact ⟨ParameterLineRecovery.recovery t ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n))
    (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) J (FirstBiextensionFactor.familyLine P φ) r⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ParameterRecovery
