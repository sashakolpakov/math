import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.IntrinsicLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicVerticalCharacter

/-! # Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.IntrinsicComparison.Intrinsic

noncomputable section

/-! Scalar balance identifies multiple-family native descent with actual pulled Poincare line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport

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

/-- An actual scalar-balancing line isomorphism intertwines the complete canonical native gluing maps. -/
theorem exists_iso :
    ∃ e : (Scheme.Modules.pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅
        (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf,
      ∀ (T : Over (Spec (.of k))) (q : T ⟶ A ⊗ A) (x y : T ⟶ A ⊗ A)
        (hx : x ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q) (hy : y ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q),
        (Scheme.Modules.pullback x.left).map e.hom ≫
          (Vertical.KernelDescent.nativeDatum ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) J).hom
            q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
        (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum (𝟙 A ⊗ₘ (𝟙 A) ^ n)
          (Line.Comparison.Bundle.toShared (FirstBiextensionFactor.familyLine P φ))).hom
            q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
          (Scheme.Modules.pullback y.left).map e.hom := by
  obtain ⟨e, hh, hv⟩ := Poincare.ScalarProductIso.exists_product_iso φ P Dh Dv hp n
  refine ⟨e, ?_⟩
  intro T q x y hx hy
  have he := IsomorphicVerticalCharacter.hom_compatible ((𝟙 A) ^ n)
    ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left) (FirstBiextensionFactor.familyLine P (φ ^ n)) e
    (Pulled.KernelFrameIsotropy.horizontalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh))
    (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) hh hv
    (PullbackKernelFrames.frames φ P Dv n) J
    (PullbackKernelFrames.transverse φ P Dh Dv n hp) hJ q x y hx hy
  exact he.trans (congrArg (fun v => v ≫ (Scheme.Modules.pullback y.left).map e.hom)
    (IntrinsicLineDescent.Intrinsic.hom_eq φ P Dv n q x y hx hy))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.IntrinsicComparison.Intrinsic
