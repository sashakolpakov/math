import OAI.ArithmeticGeometry.Models.Scheme

/-! # Foundations Pullback -/

namespace OAI.ArithmeticGeometry.Models.FoundationsPullback.Constructions

/-! Cartesian-square comparisons used by the Foundations model constructions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Pulling a map in an over category back along a fixed morphism produces
a cartesian square on its projections. -/
theorem pullback_over_map_isPullback {S X : Scheme.{u}} (x : X ⟶ S)
    {B C : Over S} (k : B ⟶ C) :
    IsPullback ((Over.pullback x).map k).left
      (pullback.fst B.hom x) (pullback.fst C.hom x) k.left := by
  have h₁ : ((Over.pullback x).map k).left ≫ pullback.fst C.hom x =
      pullback.fst B.hom x ≫ k.left := by
    dsimp [Over.pullback]
    exact pullback.lift_fst _ _ _
  have h₂ : ((Over.pullback x).map k).left ≫ pullback.snd C.hom x =
      pullback.snd B.hom x := by
    dsimp [Over.pullback]
    exact pullback.lift_snd _ _ _
  apply IsPullback.of_right ?_ h₁ (IsPullback.of_hasPullback C.hom x).flip
  rw [h₂, k.w]
  exact (IsPullback.of_hasPullback B.hom x).flip

end OAI.ArithmeticGeometry.Models.FoundationsPullback.Constructions
