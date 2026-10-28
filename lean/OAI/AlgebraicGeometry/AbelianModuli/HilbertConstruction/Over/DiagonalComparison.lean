import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Diagonal Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison

noncomputable section

/-! Comparing self-pullbacks and diagonals in the slice category with the underlying scheme constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {X Y : Over S}

def overSelfPullbackIso (f : X ⟶ Y) :
    (Limits.pullback f f).left ≅ Limits.pullback f.left f.left :=
  ((IsPullback.of_hasPullback f f).map (Over.forget S)).isoPullback

theorem overDiagonal_comparison (f : X ⟶ Y) :
    (pullback.diagonal f).left ≫ (overSelfPullbackIso f).hom = pullback.diagonal f.left := by
  let H := (IsPullback.of_hasPullback f f).map (Over.forget S)
  have hf : (overSelfPullbackIso f).hom ≫ pullback.fst f.left f.left = (pullback.fst f f).left :=
    H.isoPullback_hom_fst
  have hs : (overSelfPullbackIso f).hom ≫ pullback.snd f.left f.left = (pullback.snd f f).left :=
    H.isoPullback_hom_snd
  apply pullback.hom_ext
  · rw [Category.assoc, hf]
    exact (congrArg (fun a : X ⟶ X => a.left) (pullback.diagonal_fst f)).trans
      (pullback.diagonal_fst f.left).symm
  · rw [Category.assoc, hs]
    exact (congrArg (fun a : X ⟶ X => a.left) (pullback.diagonal_snd f)).trans
      (pullback.diagonal_snd f.left).symm

theorem formallyUnramified_of_overDiagonal (f : X ⟶ Y)
    [IsOpenImmersion (pullback.diagonal f).left] : FormallyUnramified f.left := by
  have : IsOpenImmersion (pullback.diagonal f.left) := by
    rw [← overDiagonal_comparison f]
    infer_instance
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagonalComparison
