import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Immersion Overlap Lifts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionOverlapLifts

noncomputable section

/-! Compatible closed subschemes on an overlap have the same factorization
condition on arbitrary test schemes, including nonreduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem kernel_comap_self {X Y : Scheme.{u}} (f : X ⟶ Y) : f.ker.comap f = ⊥ := by
  apply bot_unique
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  rw [Scheme.IdealSheafData.map_bot]

theorem closedImmersion_overlap_lift
    {X V₁ V₂ Z₁ Z₂ W : Scheme.{u}} (u₁ : V₁ ⟶ X) (u₂ : V₂ ⟶ X)
    (c₁ : Z₁ ⟶ V₁) (c₂ : Z₂ ⟶ V₂) [IsClosedImmersion c₂]
    (hc : c₁.ker.comap (pullback.fst u₁ u₂) = c₂.ker.comap (pullback.snd u₁ u₂))
    (a : W ⟶ Z₁) (b : W ⟶ V₂) (h : a ≫ c₁ ≫ u₁ = b ≫ u₂) :
    ∃ l : W ⟶ Z₂, l ≫ c₂ = b := by
  let w : W ⟶ pullback u₁ u₂ := pullback.lift (a ≫ c₁) b ((Category.assoc _ _ _).trans h)
  have he := congrArg (fun I => I.comap w) hc
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    show w ≫ pullback.fst u₁ u₂ = a ≫ c₁ from pullback.lift_fst _ _ _,
    show w ≫ pullback.snd u₁ u₂ = b from pullback.lift_snd _ _ _,
    Scheme.IdealSheafData.comap_comp, kernel_comap_self, Scheme.IdealSheafData.comap_bot] at he
  have hk : c₂.ker ≤ b.ker := by
    rw [← Scheme.IdealSheafData.map_bot b, Scheme.IdealSheafData.le_map_iff_comap_le]
    exact he.ge
  exact ⟨IsClosedImmersion.lift c₂ b hk, IsClosedImmersion.lift_fac c₂ b hk⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionOverlapLifts
