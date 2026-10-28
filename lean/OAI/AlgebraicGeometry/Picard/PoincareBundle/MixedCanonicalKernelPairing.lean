import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.PairingValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

/-! # Mixed Canonical Kernel Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MixedCanonicalKernelPairing

noncomputable section

/-! Mixed actual subgroup kernels compute the same canonical full-kernel pairing and its full orthogonal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.FrameIndependence

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B C Z : Over S} [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
  (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1) (hg : Kernel.Scheme.kernelInclusion g ≫ φ = 1)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) e = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (i : Kernel.Scheme.kernelObject f ⟶ Kernel.Scheme.kernelObject φ) (j : Kernel.Scheme.kernelObject g ⟶ Kernel.Scheme.kernelObject φ)
  (hi : i ≫ Kernel.Scheme.kernelInclusion φ = Kernel.Scheme.kernelInclusion f) (hj : j ≫ Kernel.Scheme.kernelInclusion φ = Kernel.Scheme.kernelInclusion g)

include hi hj

/-- The full-kernel value is the actual ratio of the two canonical frames on their different subgroup presentations. -/
theorem value_at_mixed {T : Over S} (x : T ⟶ Kernel.Scheme.kernelObject f) (y : T ⟶ Kernel.Scheme.kernelObject g)
    (a : T ⟶ A ⊗ A) (hx : x ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A A)
    (hy : y ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A A) :
    Canonical.KernelPairing.value φ P Dh Dv φ (Kernel.Scheme.kernelInclusion_comp φ) e hv (x ≫ i) (y ≫ j) =
      Biextension.Compatibility.kernelObstruction (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) f g
        (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv g hg e hv) x y a hx hy := by
  have hx' : (x ≫ i) ≫ Kernel.Scheme.kernelInclusion φ = a ≫ fst A A := by rw [Category.assoc, hi, hx]
  have hy' : (y ≫ j) ≫ Kernel.Scheme.kernelInclusion φ = a ≫ snd A A := by rw [Category.assoc, hj, hy]
  refine (Canonical.KernelPairing.value_at φ P Dh Dv φ (Kernel.Scheme.kernelInclusion_comp φ) e hv
    (x ≫ i) (y ≫ j) a hx' hy').trans ?_
  exact congrArg₂ Line.FrameUnits.frameRatio
    (Canonical.FrameIndependence.first_frame_eq φ P Dh φ f (Kernel.Scheme.kernelInclusion_comp φ) hf (x ≫ i) x a hx' hx)
    (Canonical.FrameIndependence.second_frame_eq φ P Dh φ g (Kernel.Scheme.kernelInclusion_comp φ) hg Dv e hv (y ≫ j) y a hy' hy)

variable (hp : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) f g
    (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv g hg e hv))

include he

/-- Vanishing of the mixed frame obstruction places every point of the second subgroup in the full right orthogonal. -/
theorem mem_orthogonal {T : Over S} (y : T ⟶ Kernel.Scheme.kernelObject g) :
    y ≫ j ∈ NaturalPairingOrthogonal.orthogonal i
      (Canonical.KernelPairing.pairing φ P Dh Dv φ (Kernel.Scheme.kernelInclusion_comp φ) e hv hp hh) T := by
  intro U a x
  rw [← Category.assoc a y j, Canonical.PairingValues.pairing_apply]
  let c := Biextension.KernelRectangle.crossPoint f g x (a ≫ y)
  have hx : x ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A A :=
    (Biextension.KernelRectangle.crossPoint_fst f g x (a ≫ y)).symm
  have hy : (a ≫ y) ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A A :=
    (Biextension.KernelRectangle.crossPoint_snd f g x (a ≫ y)).symm
  exact (value_at_mixed φ P Dh Dv f g hf hg e hv i j hi hj x (a ≫ y) c hx hy).trans
    (he U x (a ≫ y) c hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MixedCanonicalKernelPairing
