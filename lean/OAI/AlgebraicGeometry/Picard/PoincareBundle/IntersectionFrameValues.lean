import OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFramePullbacks

/-! # Intersection Frame Values -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFrameValues

noncomputable section

/-! The two global intersection frames evaluate as the two original frames at every scheme-valued pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {S : Scheme.{u}} {H K A B : Over S} (i : H ⟶ A) (j : K ⟶ B)
  (Q : Line.Bundles.LineBundle (A ⊗ B).left)
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ B).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 B).left).obj Q.sheaf)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ K).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ j).left).obj Q.sheaf)

theorem horizontal_pair {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    lift a (b ≫ j) ≫ (i ⊗ₘ 𝟙 B) = lift (a ≫ i) (b ≫ j) := by
  rw [lift_map, Category.comp_id]

theorem vertical_pair {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    lift (a ≫ i) b ≫ (𝟙 A ⊗ₘ j) = lift (a ≫ i) (b ≫ j) := by
  rw [lift_map, Category.comp_id]

theorem horizontal_evaluation {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    FrameRatioPullback.pullFrame (lift a b).left (Kernel.IntersectionFrames.horizontalFrame i j Q s) ≪≫
        Line.Fibers.fiberPullbackIso Q (lift a b) (i ⊗ₘ j) (lift (a ≫ i) (b ≫ j)) (lift_map a b i j) =
      GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 B) Q s (lift a (b ≫ j))
        (lift (a ≫ i) (b ≫ j)) (horizontal_pair i j a b) := by
  have h₁ : lift a b ≫ (𝟙 H ⊗ₘ j) = lift a (b ≫ j) := by rw [lift_map, Category.comp_id]
  rw [IntersectionFramePullbacks.horizontal_eq]
  exact GlobalFrameNaturality.atPoint_pullback (i ⊗ₘ 𝟙 B) Q s (lift a b) (𝟙 H ⊗ₘ j)
    (i ⊗ₘ j) (Kernel.IntersectionFrames.horizontal_factor i j) (lift a (b ≫ j)) (lift (a ≫ i) (b ≫ j))
    (horizontal_pair i j a b) h₁ (lift_map a b i j)

theorem vertical_evaluation {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    FrameRatioPullback.pullFrame (lift a b).left (Kernel.IntersectionFrames.verticalFrame i j Q t) ≪≫
        Line.Fibers.fiberPullbackIso Q (lift a b) (i ⊗ₘ j) (lift (a ≫ i) (b ≫ j)) (lift_map a b i j) =
      GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ j) Q t (lift (a ≫ i) b)
        (lift (a ≫ i) (b ≫ j)) (vertical_pair i j a b) := by
  have h₁ : lift a b ≫ (i ⊗ₘ 𝟙 K) = lift (a ≫ i) b := by rw [lift_map, Category.comp_id]
  rw [IntersectionFramePullbacks.vertical_eq]
  exact GlobalFrameNaturality.atPoint_pullback (𝟙 A ⊗ₘ j) Q t (lift a b) (i ⊗ₘ 𝟙 K)
    (i ⊗ₘ j) (Kernel.IntersectionFrames.vertical_factor i j) (lift (a ≫ i) b) (lift (a ≫ i) (b ≫ j))
    (vertical_pair i j a b) h₁ (lift_map a b i j)

/-- Triviality of the actual obstruction identifies the original frames on every test-scheme pair. -/
theorem isotropic_values
    (hi : ∀ (T : Over S) (a : T ⟶ H) (b : T ⟶ K), Kernel.IntersectionFrames.obstruction i j Q s t a b = 1)
    {T : Over S} (a : T ⟶ H) (b : T ⟶ K) :
    GlobalPullbackFrame.atPoint (i ⊗ₘ 𝟙 B) Q s (lift a (b ≫ j))
        (lift (a ≫ i) (b ≫ j)) (horizontal_pair i j a b) =
      GlobalPullbackFrame.atPoint (𝟙 A ⊗ₘ j) Q t (lift (a ≫ i) b)
        (lift (a ≫ i) (b ≫ j)) (vertical_pair i j a b) := by
  have he := (Kernel.IntersectionFrames.obstruction_trivial_iff i j Q s t).mp hi
  have hp := congrArg (fun f => FrameRatioPullback.pullFrame (lift a b).left f ≪≫
    Line.Fibers.fiberPullbackIso Q (lift a b) (i ⊗ₘ j) (lift (a ≫ i) (b ≫ j)) (lift_map a b i j)) he
  exact (horizontal_evaluation i j Q s a b).symm.trans (hp.trans (vertical_evaluation i j Q t a b))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.IntersectionFrameValues
