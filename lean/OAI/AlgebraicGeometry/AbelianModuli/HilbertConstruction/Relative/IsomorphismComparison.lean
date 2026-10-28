import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianMorphismIsomorphismComparison
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Isomorphism Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IsomorphismComparison

noncomputable section

/-! The actual pullback of an over-scheme morphism has the same isomorphism condition as the canonical relative scheme map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem overPullback_map_isIso_iff_relativeMorphismBaseChange
    {S T : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) (c : T ⟶ S) :
    IsIso ((Over.pullback c).map j) ↔ IsIso (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange j.left Y.hom c) := by
  let m := (Over.pullback c).map j
  have hX : IsPullback (pullback.fst X.hom c) (pullback.snd X.hom c) (j.left ≫ Y.hom) c := by
    rw [j.w]
    exact IsPullback.of_hasPullback X.hom c
  have hk : m.left ≫ pullback.fst Y.hom c = pullback.fst X.hom c ≫ j.left := by
    simp only [m, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hr : m.left ≫ pullback.snd Y.hom c = pullback.snd X.hom c := m.w
  have h := HilbertScheme.Presentations.CartesianMorphismIsomorphismComparison.relativeMorphismBaseChange_isIso_iff_cartesian_comparison
    j.left Y.hom c _ _ _ _ m.left hX (IsPullback.of_hasPullback Y.hom c) hk hr
  have hm : IsIso m ↔ IsIso m.left := by
    constructor
    · intro h
      have : IsIso m := h
      exact (Over.forget T).map_isIso m
    · intro h
      have : IsIso ((Over.forget T).map m) := h
      exact isIso_of_reflects_iso m (Over.forget T)
  exact hm.trans h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IsomorphismComparison
