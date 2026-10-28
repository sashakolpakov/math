import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalGlobalCoefficientBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback

/-! # Bounded Choice Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Construct new finite coefficient-choice atlases with the same prescribed bound after étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Component.CenterChoice.Construction.ComponentCenterChoice.ordinary_bound
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n : ℕ}
    (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤ := by
  cases C with
  | terminal ht =>
      exact top_le_iff.mp (ht ▸ Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J (Nat.le_succ n))
  | normal z D hD hz =>
      rw [Ideal.eq_top_iff_one, Relative.DifferentialProducts.Construction.iteratedRelativeDifferentialIdeal_add k J n 1]
      exact hD ▸ Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) D hz

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.ordinary_bound
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤ := by
  apply Finite.OpenIdealSheafUniqueness.Construction.idealSheaf_eq_of_open_affine_restrictions (fun i => Spec (A.rings i)) A.map A.cover
  intro i
  rw [Scheme.IdealSheafData.comap_top]
  exact DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_unit_on_affine f J (n + 1) (A.map i) (A.ground i)
    (A.ideals i) (A.ideal_eq i) (A.choice i).ordinary_bound

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.exists_bounded_etale_pullback
    {X V : Scheme} [CompactSpace V] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J : X.IdealSheafData} {n : ℕ} (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ)
    (hb : ∀ i, (A.choice i).HasBound m) (q : V ⟶ X) [Etale q] :
    ∃ B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (q ≫ f) (J.comap q) n, ∀ i, (B.choice i).HasBound m := by
  have hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) (n + 1) = ⊤ := by
    rw [← Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, A.ordinary_bound, Scheme.IdealSheafData.comap_top]
  obtain ⟨B⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas (q ≫ f) (J.comap q) n hbound
  exact ⟨B, A.hasBound_comap_etale m hb q B⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
