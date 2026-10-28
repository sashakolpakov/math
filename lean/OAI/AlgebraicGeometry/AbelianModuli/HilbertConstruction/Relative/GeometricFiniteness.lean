import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.GeometricFiberFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Geometric Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GeometricFiniteness

noncomputable section

/-! Finiteness of a proper morphism between relative schemes can be checked after every algebraically closed field base change of the common base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_overMap_isFinite_of_geometric_baseChange
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsProper f.left]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      IsFinite ((Over.pullback s).map f).left) : IsFinite f.left := by
  apply Proper.GeometricFiberFiniteness.proper_isFinite_of_geometric_fieldPullbacks f.left
  intro K _ _ a
  let s := a ≫ Y.hom
  let b : Spec (.of K) ⟶ ((Over.pullback s).obj Y).left :=
    Limits.pullback.lift a (𝟙 _) (Category.id_comp s).symm
  let g := ((Over.pullback s).map f).left
  have : IsFinite g := h K s
  let q := Limits.pullback.snd g b
  have : IsFinite q := inferInstanceAs (IsFinite (Limits.pullback.snd g b))
  have H : IsPullback (Limits.pullback.fst g b ≫ Limits.pullback.fst X.hom s)
      q f.left (b ≫ Limits.pullback.fst Y.hom s) :=
    (IsPullback.of_hasPullback g b).paste_horiz (Projective.PresentationBaseChange.overPullback_map_isPullback f s)
  have hb : b ≫ Limits.pullback.fst Y.hom s = a := Limits.pullback.lift_fst _ _ _
  have H' : IsPullback (Limits.pullback.fst g b ≫ Limits.pullback.fst X.hom s) q f.left a := hb ▸ H
  have hq : IsFinite (H'.isoPullback.inv ≫ q) := inferInstance
  exact H'.isoPullback_inv_snd ▸ hq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GeometricFiniteness
