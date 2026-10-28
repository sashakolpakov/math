import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarProductIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphicKernelFrames

/-! # Pullback Kernel Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackKernelFrames

noncomputable section

/-! Scalar balance identifies the canonical second-kernel frames with the actual unit frames of the multiplication pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-- Equality of the quotient morphism transports the complete actual kernel-frame system. -/
def congr_quotient {S : Scheme.{u}} {A : Over S} [GrpObj A] (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (h : f = g) (L : Line.Bundles.LineBundle (A ⊗ A).left)
    (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L) (K : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L f Dv) :
    FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L g Dv := by
  cases h
  exact K

/-- The same equality transports the proved transverse law. -/
theorem congr_quotient_transverse {S : Scheme.{u}} {A : Over S} [GrpObj A]
    (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (h : f = g) (L : Line.Bundles.LineBundle (A ⊗ A).left)
    (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L) (K : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L f Dv)
    (Dh : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L) (ht : Kernel.FramesTransverseTransport.Transverse f K Dh) :
    Kernel.FramesTransverseTransport.Transverse g (congr_quotient f g h L Dv K) Dh := by
  cases h
  exact ht

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)

/-- The actual target unit frames pull back to the full n-torsion kernel, with its original kernel presentation. -/
def frames : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
    ((𝟙 A) ^ n) (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv)) :=
  congr_quotient (((𝟙 A) ^ n) ≫ 𝟙 A) ((𝟙 A) ^ n) (Category.comp_id _)
    ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
    (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Pulled.KernelFrameIsotropy.vertical (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))

/-- These actual scalar-cover unit frames respect the first product. -/
theorem transverse (hp : Biextension.Compatibility.Interchange P Dh Dv) :
    Kernel.FramesTransverseTransport.Transverse ((𝟙 A) ^ n) (frames φ P Dv n)
      (Pulled.KernelFrameIsotropy.horizontalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)) :=
  congr_quotient_transverse (((𝟙 A) ^ n) ≫ 𝟙 A) ((𝟙 A) ^ n) (Category.comp_id _)
    ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
    (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Pulled.KernelFrameIsotropy.vertical (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Pulled.KernelFrameIsotropy.horizontalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh))
    (Pulled.KernelFrameIsotropy.vertical_transverse (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ)
      (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hp))

variable {k : Type u} [Field k] {A Z : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj Z] [IsCommMonObj Z]

/-- The scalar-balancing isomorphism identifies any genuine transverse multiple-family frames with the scalar-cover unit frames. -/
theorem exists_frame_iso (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (hp : Biextension.Compatibility.Interchange P Dh Dv) (n : ℕ) [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A) ^ n)).left]
    (J : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (FirstBiextensionFactor.familyLine P (φ ^ n)) ((𝟙 A) ^ n) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv))
    (hJ : Kernel.FramesTransverseTransport.Transverse ((𝟙 A) ^ n) J (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)) :
    ∃ e : (Scheme.Modules.pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅
        (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf,
      ∀ (T : Over (Spec (.of k))) (l : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) (c : T ⟶ A ⊗ A)
        (hc : l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n) = c ≫ snd A A),
        Line.FiberIsomorphisms.transportFrame ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
          (FirstBiextensionFactor.familyLine P (φ ^ n)) e c ((frames φ P Dv n).frame l c hc) = J.frame l c hc := by
  obtain ⟨e, hh, hv⟩ := Poincare.ScalarProductIso.exists_product_iso φ P Dh Dv hp n
  refine ⟨e, ?_⟩
  intro T l c hc
  exact IsomorphicKernelFrames.vertical_frame ((𝟙 A) ^ n)
    ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left) (FirstBiextensionFactor.familyLine P (φ ^ n)) e
    (Pulled.KernelFrameIsotropy.horizontalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh))
    (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) hh hv
    (frames φ P Dv n) J (transverse φ P Dh Dv n hp) hJ l c hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.PullbackKernelFrames
