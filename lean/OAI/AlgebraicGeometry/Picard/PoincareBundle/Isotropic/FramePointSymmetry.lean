import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginFrameComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionSymmetry

/-! # Frame Point Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.FramePointSymmetry

noncomputable section

/-! Scheme-valued isotropy identifies the Poincare frames at an exchanged pair through the actual symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {S : Scheme.{u}} {H A : Over S} (i : H ⟶ A)
  (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)

theorem exchanged_pair {T : Over S} (a b : T ⟶ H) :
    lift b (a ≫ i) ≫ (i ⊗ₘ 𝟙 A) = lift (a ≫ i) (b ≫ i) ≫ (β_ A A).hom := by
  rw [lift_map, Category.comp_id, lift_braiding_hom]

/-- The frame over the exchanged pair is carried to the original frame by the actual Poincare symmetry. -/
theorem frame_symmetry
    (hi : ∀ (T : Over S) (a b : T ⟶ H),
      Kernel.IntersectionFrames.obstruction i i Q s (Symmetric.KernelTrivialization.secondFrame i Q s σ) a b = 1)
    {T : Over S} (a b : T ⟶ H) :
    GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) Q s (lift b (a ≫ i))
        (lift (a ≫ i) (b ≫ i) ≫ (β_ A A).hom) (exchanged_pair i a b) ≪≫
      Line.SymmetryFibers.atPoint Q (β_ A A).hom σ (lift (a ≫ i) (b ≫ i)) =
    GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 A) Q s (lift a (b ≫ i))
      (lift (a ≫ i) (b ≫ i)) (IntersectionFrameValues.horizontal_pair i i a b) := by
  have hv := SymmetryTransportedFrames.evaluation (i ⊗ₘ 𝟙 A) Q s (β_ A A).hom σ
    (β_ A H).hom (𝟙 A ⊗ₘ i) (Symmetric.KernelTrivialization.exchange_square i).symm
    (lift (a ≫ i) b) (lift b (a ≫ i)) (lift (a ≫ i) (b ≫ i))
    (IntersectionFrameValues.vertical_pair i i a b) (lift_braiding_hom _ _) (exchanged_pair i a b)
  have he := IntersectionFrameValues.isotropic_values i i Q s
    (Symmetric.KernelTrivialization.secondFrame i Q s σ) hi a b
  have ht := Kernel.IntersectionSymmetry.secondFrame_eq i Q s σ
  have ht' := congrArg (fun t => GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ i) Q t
    (lift (a ≫ i) b) (lift (a ≫ i) (b ≫ i)) (IntersectionFrameValues.vertical_pair i i a b)) ht
  exact hv.symm.trans (ht'.symm.trans he.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.FramePointSymmetry
