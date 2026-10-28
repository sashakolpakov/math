import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.MultiplicationUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarLineIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.OriginNormalization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits

/-! # Scalar Product Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarProductIso

noncomputable section

/-! The actual scalar-balancing Poincare line isomorphism can be normalized to preserve both complete products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso

variable {k : Type u} [Field k] {A Z : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj Z] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hp : Biextension.Compatibility.Interchange P Dh Dv) (n : ℕ)

include hp

/-- Scalar balance is realized by an actual line isomorphism preserving both products, in arbitrary characteristic. -/
theorem exists_product_iso :
    ∃ e : (Scheme.Modules.pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅
        (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf,
      FiberwiseMultiplicationIso.transportMultiplication (fst A A) (snd A A)
        ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left) (FirstBiextensionFactor.familyLine P (φ ^ n)) e
        (Pulled.KernelFrameIsotropy.horizontalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)) =
        Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh ∧
      FiberwiseMultiplicationIso.transportMultiplication (snd A A) (fst A A)
        ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left) (FirstBiextensionFactor.familyLine P (φ ^ n)) e
        (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (TransverseFrames.sourceVertical φ P Dv)) =
        TransverseFrames.sourceVertical (φ ^ n) P Dv := by
  have hu (T : Over (Spec (.of k))) : Dh.unitFrame (1 : T ⟶ Z ⊗ A) (MonObj.one_comp (fst Z A)) =
      Dv.unitFrame 1 (MonObj.one_comp (snd Z A)) :=
    Biextension.OriginNormalization.unitFrames_eq P Dh Dv hp 1
      (MonObj.one_comp (fst Z A)) (MonObj.one_comp (snd Z A))
  have hs (T : Over (Spec (.of k))) := AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits.Construction.sourceMultiplications_unit_zero φ P Dh Dv T (hu T)
  have ht (T : Over (Spec (.of k))) := AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits.Construction.sourceMultiplications_unit_zero (φ ^ n) P Dh Dv T (hu T)
  exact Biextension.OriginNormalization.exists_productCompatible_iso A A
    ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left) (FirstBiextensionFactor.familyLine P (φ ^ n))
    (Pulled.KernelFrameIsotropy.horizontalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh))
    (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (TransverseFrames.sourceVertical φ P Dv))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (TransverseFrames.sourceVertical (φ ^ n) P Dv)
    (ScalarLineIso.scalarIso P Dh Dv φ n)
    (Pulled.MultiplicationUnits.unitFrames_eq (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ)
      (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (TransverseFrames.sourceVertical φ P Dv) _ (hs _)) (ht _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarProductIso
