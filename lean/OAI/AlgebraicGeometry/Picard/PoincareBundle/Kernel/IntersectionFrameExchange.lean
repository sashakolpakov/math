import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFramePullbacks
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SymmetryTransportedFrames

/-! # Intersection Frame Exchange -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrameExchange

noncomputable section

/-! Isotropy makes the actual frame on the full kernel intersection invariant under symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {S : Scheme.{u}} {H A : Over S} (i : H ⟶ A)
  (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)

theorem exchanged_factor :
    ((β_ H H).hom ≫ (𝟙 H ⊗ₘ i)) ≫ (i ⊗ₘ 𝟙 A) = (i ⊗ₘ i) ≫ (β_ A A).hom := by
  rw [Category.assoc, IntersectionFrames.horizontal_factor, IntersectionSymmetry.swap_square]

/-- Exchanging the first frame gives exactly the canonical second frame on the intersection. -/
theorem frame_exchange :
    FrameRatioPullback.pullFrame (β_ H H).hom.left (IntersectionFrames.horizontalFrame i i Q s) ≪≫
        IntersectionSymmetry.symmetry i Q σ =
      IntersectionFrames.verticalFrame i i Q (Symmetric.KernelTrivialization.secondFrame i Q s σ) := by
  have hh := GlobalFrameNaturality.atPoint_pullback (i ⊗ₘ 𝟙 A) Q s
    (β_ H H).hom (𝟙 H ⊗ₘ i) (i ⊗ₘ i) (IntersectionFrames.horizontal_factor i i)
    ((β_ H H).hom ≫ (𝟙 H ⊗ₘ i)) ((i ⊗ₘ i) ≫ (β_ A A).hom)
    (exchanged_factor i) rfl (IntersectionSymmetry.swap_square i)
  have hv := SymmetryTransportedFrames.evaluation (i ⊗ₘ 𝟙 A) Q s (β_ A A).hom σ
    (β_ A H).hom (𝟙 A ⊗ₘ i) (Symmetric.KernelTrivialization.exchange_square i).symm
    (i ⊗ₘ 𝟙 H) ((β_ H H).hom ≫ (𝟙 H ⊗ₘ i)) (i ⊗ₘ i)
    (IntersectionFrames.vertical_factor i i) (BraidedCategory.braiding_naturality i (𝟙 H)) (exchanged_factor i)
  rw [IntersectionFramePullbacks.horizontal_eq, IntersectionFramePullbacks.vertical_eq,
    IntersectionSymmetry.secondFrame_eq]
  exact (Iso.trans_assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≪≫ Line.SymmetryFibers.atPoint Q (β_ A A).hom σ (i ⊗ₘ i)) hh).trans hv.symm)

/-- Scheme-valued isotropy, including infinitesimal test schemes, gives an invariant actual frame. -/
theorem isotropic_frame (hi : ∀ (T : Over S) (a b : T ⟶ H),
    IntersectionFrames.obstruction i i Q s (Symmetric.KernelTrivialization.secondFrame i Q s σ) a b = 1) :
    FrameRatioPullback.pullFrame (β_ H H).hom.left (IntersectionFrames.horizontalFrame i i Q s) ≪≫
      IntersectionSymmetry.symmetry i Q σ = IntersectionFrames.horizontalFrame i i Q s :=
  (frame_exchange i Q s σ).trans
    ((IntersectionFrames.obstruction_trivial_iff i i Q s (Symmetric.KernelTrivialization.secondFrame i Q s σ)).mp hi).symm

/-- The same invariant frame satisfies the actual section equation used in bilinear contraction. -/
theorem isotropic_section (hi : ∀ (T : Over S) (a b : T ⟶ H),
    IntersectionFrames.obstruction i i Q s (Symmetric.KernelTrivialization.secondFrame i Q s σ) a b = 1) :
    Bilinear.ContractionPullback.pulledSection (β_ H H).hom.left (IntersectionFrames.horizontalFrame i i Q s).hom ≫
      (IntersectionSymmetry.symmetry i Q σ).hom = (IntersectionFrames.horizontalFrame i i Q s).hom :=
  congrArg Iso.hom (isotropic_frame i Q s σ hi)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrameExchange
