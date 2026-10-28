import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TransverseFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.BiextensionLineDescent

/-! # Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent

noncomputable section

/-!
# Effective line descent for the canonical isotropic Poincare kernel frames

Scheme-theoretic annihilation, the genuine Poincare products, and their product-exchanging
symmetry construct both full kernel-frame systems. Interchange and both transverse laws are
proved from the original products. Only isotropy of their actual unit-valued obstruction is
required for descent; no kernel splitting, action, cocycle, or descended line is assumed.

Identifying this obstruction with the polarization Weil pairing and representing the descended
biextension by the desired polarization remain separate mathematical steps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hi : Biextension.Compatibility.Interchange P Dh Dv) (f : A ⟶ B) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) symmetry = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)

/-- The second actual multiplicative kernel frames are constructed from Poincare symmetry. -/
def secondKernelFrames : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (FirstBiextensionFactor.familyLine P φ) f (Poincare.TransverseFrames.sourceVertical φ P Dv) :=
  Symmetric.TransverseFrames.secondFramesOfCompatible (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) hv

include hi hh in
omit [IsCommMonObj A] in
/-- Both transverse laws of the constructed Poincare frames follow from original interchange and symmetry. -/
theorem transverse_frames : Biextension.Compatibility.TransverseFrames (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (Poincare.TransverseFrames.sourceVertical φ P Dv) f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (secondKernelFrames φ P Dh Dv f hφ symmetry hv) :=
  Symmetric.TransverseFrames.transverseFrames (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) hv hh
    (fun _T k a b c ha hb hc h U => Poincare.TransverseFrames.kernel_frames_transverse φ P Dh Dv hi f hφ k a b c ha hb hc h U)

variable (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
  f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (secondKernelFrames φ P Dh Dv f hφ symmetry hv))

/-- The actual isotropic Poincare frames construct the full ordinary quotient descent datum. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData
    (fun (_ : PUnit.{1}) => (f ⊗ₘ f).left) :=
  Isotropic.BiextensionLineDescent.ordinaryDatum f f (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ)
    (secondKernelFrames φ P Dh Dv f hφ symmetry hv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hi)
    (transverse_frames φ P Dh Dv hi f hφ symmetry hv hh) he

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

/-- The invariant sheaf of the constructed canonical actions is an actual line bundle on the quotient product. -/
def descendedLine : Line.Bundles.LineBundle (B ⊗ B).left :=
  Isotropic.BiextensionLineDescent.descendedLine f f (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ)
    (secondKernelFrames φ P Dh Dv f hφ symmetry hv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hi)
    (transverse_frames φ P Dh Dv hi f hφ symmetry hv hh) he

/-- The constructed quotient line pulls back to the actual Poincare line associated with the original homomorphism. -/
def pullbackIso : (Scheme.Modules.pullback (f ⊗ₘ f).left).obj
    (descendedLine φ P Dh Dv hi f hφ symmetry hv hh he).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf :=
  Isotropic.BiextensionLineDescent.pullbackIso f f (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ)
    (secondKernelFrames φ P Dh Dv f hφ symmetry hv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hi)
    (transverse_frames φ P Dh Dv hi f hφ symmetry hv hh) he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
