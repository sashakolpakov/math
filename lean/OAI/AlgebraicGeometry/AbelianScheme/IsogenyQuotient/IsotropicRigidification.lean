import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardSheaf
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.SecondUnitFrame
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine

/-! # Isotropic Rigidification -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicRigidification.Construction

noncomputable section

/-! The actual neutral frame of the descended Poincare line supplies
the rigidification required by normalized-frame kernel representability. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

universe u
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {k : Type u} [Field k] {A B Z : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj Z] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)
  (f : A ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (Poincare.LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh).relativeAnnihilator F = F)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian B.left]

def nativeIsotropicQuotientRigidifiedLine : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B where
  bundle := Poincare.LineDescent.Construction.nativeIsotropicQuotientLine φ P Dh Dv n e hv hi hh f hker hlag
  axis := (Picard.PoincareBundle.CanonicalPoincare.SecondUnitFrame.unitFrame (φ ^ n) P Dh Dv hi f
    (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
    (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
      (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag))).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicRigidification.Construction
