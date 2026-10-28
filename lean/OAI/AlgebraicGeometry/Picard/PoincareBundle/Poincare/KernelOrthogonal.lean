import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.KernelIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.KernelIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MixedCanonicalKernelPairing

/-! # Kernel Orthogonal -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelOrthogonal

noncomputable section

/-! Recovery of the actual quotient Poincare family places its inverse-image kernel in the full canonical orthogonal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type u} [Field k] {A B C Z : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f] (m : B ⟶ C) [IsMonHom m]
  [IsAffine (Kernel.Scheme.kernelObject (f ≫ m)).left] [IsAffine (Kernel.Scheme.kernelObject (f ≫ 𝟙 B)).left]
  (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (Q : Line.Bundles.LineBundle (C ⊗ B).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst C B) (snd C B) Q) (Qv : FiberwiseMultiplication.Multiplication (snd C B) (fst C B) Q)
  (hq : Biextension.Compatibility.Interchange Q Qh Qv)
  (hN : Kernel.Scheme.kernelInclusion (f ≫ m) ≫ φ = 1) (hH : Kernel.Scheme.kernelInclusion (f ≫ 𝟙 B) ≫ φ = 1)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) σ = TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (TransverseFrames.sourceVertical φ P Dv) σ =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (e : ((FirstBiextensionFactor.familyLine Q m).pullback (f ⊗ₘ f).left).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)

include hp hq hh e hN hH

/-- The quotient Poincare kernel frames and actual recovery force inverse-image-first isotropy. -/
theorem inverseImage_isotropic : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (TransverseFrames.sourceVertical φ P Dv) (f ≫ m) (f ≫ 𝟙 B)
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh (f ≫ m) hN) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv (f ≫ 𝟙 B) hH σ hv) := by
  exact Recovered.KernelIsotropy.isotropic f m (FirstBiextensionFactor.familyLine Q m)
    (Pulled.KernelFrames.Poincare.sourceMultiplication m Q Qh) (TransverseFrames.sourceVertical m Q Qv)
    (Pulled.KernelFrames.Poincare.kernelFrames m Q Qh m (Kernel.Scheme.kernelInclusion_comp m))
    (fun _T x a b c ha hb hc h U => TransverseFrames.kernel_frames_transverse m Q Qh Qv hq m
      (Kernel.Scheme.kernelInclusion_comp m) x a b c ha hb hc h U)
    (TransverseFrames.source_interchange m Q Qh Qv hq) (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (TransverseFrames.sourceVertical φ P Dv)
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh (f ≫ m) hN) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv (f ≫ 𝟙 B) hH σ hv)
    (fun _T x a b c ha hb hc h U => TransverseFrames.kernel_frames_transverse φ P Dh Dv hp (f ≫ m) hN x a b c ha hb hc h U)
    (CanonicalPoincare.LineDescent.transverse_frames φ P Dh Dv hp (f ≫ 𝟙 B) hH σ hv hh).1 e

/-- Actual source Poincare symmetry reverses the arguments to the convention of the full right orthogonal. -/
theorem quotientKernel_isotropic : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (TransverseFrames.sourceVertical φ P Dv) (f ≫ 𝟙 B) (f ≫ m)
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh (f ≫ 𝟙 B) hH) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv (f ≫ m) hN σ hv) := by
  have tN := CanonicalPoincare.LineDescent.transverse_frames φ P Dh Dv hp (f ≫ m) hN σ hv hh
  have tH := CanonicalPoincare.LineDescent.transverse_frames φ P Dh Dv hp (f ≫ 𝟙 B) hH σ hv hh
  exact Symmetric.KernelIsotropy.flip (f ≫ m) (f ≫ 𝟙 B) (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (TransverseFrames.sourceVertical φ P Dv) σ
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh (f ≫ m) hN) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv (f ≫ m) hN σ hv)
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh (f ≫ 𝟙 B) hH) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv (f ≫ 𝟙 B) hH σ hv)
    tN.2 tN.1 tH.2 tH.1 (inverseImage_isotropic f m φ P Dh Dv hp Q Qh Qv hq hN hH σ hv hh e)

/-- Every scheme-valued inverse-image kernel point belongs to the full orthogonal after every further base change. -/
theorem mem_orthogonal (i : Kernel.Scheme.kernelObject (f ≫ 𝟙 B) ⟶ Kernel.Scheme.kernelObject φ)
    (j : Kernel.Scheme.kernelObject (f ≫ m) ⟶ Kernel.Scheme.kernelObject φ)
    (hi : i ≫ Kernel.Scheme.kernelInclusion φ = Kernel.Scheme.kernelInclusion (f ≫ 𝟙 B))
    (hj : j ≫ Kernel.Scheme.kernelInclusion φ = Kernel.Scheme.kernelInclusion (f ≫ m))
    {T : Over (Spec (.of k))} (y : T ⟶ Kernel.Scheme.kernelObject (f ≫ m)) :
    y ≫ j ∈ NaturalPairingOrthogonal.orthogonal i
      (Canonical.KernelPairing.pairing φ P Dh Dv φ (Kernel.Scheme.kernelInclusion_comp φ) σ hv hp hh) T :=
  MixedCanonicalKernelPairing.mem_orthogonal φ P Dh Dv (f ≫ 𝟙 B) (f ≫ m) hH hN σ hv i j hi hj hp hh
    (quotientKernel_isotropic f m φ P Dh Dv hp Q Qh Qv hq hN hH σ hv hh e) y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelOrthogonal
