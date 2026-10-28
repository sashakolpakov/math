import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.IntrinsicComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.LineRecovery

/-! # Descent Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.DescentRecovery

noncomputable section

/-! The original Poincare family recovers the entire ordinary scalar-kernel descent datum. -/

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

include hp hJ

/-- Scalar balance gives recovery as an actual descent-category isomorphism. -/
theorem exists_recovery :
    Nonempty ((Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks)
      (f := fun (_ : PUnit.{1}) => (𝟙 A ⊗ₘ (𝟙 A) ^ n).left) (FirstBiextensionFactor.familyLine P φ).sheaf) ≅
        Vertical.KernelDescent.ordinaryDatum ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) J) := by
  obtain ⟨e, he⟩ := IntrinsicComparison.Intrinsic.exists_iso φ P Dh Dv hp n J hJ
  exact ⟨Intrinsic.LineRecovery.iso (𝟙 A ⊗ₘ (𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) _ e he⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.DescentRecovery
