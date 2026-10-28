import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedComparisonIso

/-! # Map Realization Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MapRealizationIso

noncomputable section

/-! Isomorphism of a Cartesian realization implies isomorphism of the canonical pullback map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]

theorem isIso_pullback_map_of_isIso_realization
    {A B S S₀ A' B' : C} (a : A ⟶ S₀) (b : B ⟶ S₀) (c : S ⟶ S₀)
    (f : A ⟶ B) (hf : f ≫ b = a) [HasPullback a c] [HasPullback b c]
    (rA : A' ⟶ A) (rB : B' ⟶ B) (sA : A' ⟶ S) (sB : B' ⟶ S)
    (hA : IsPullback rA sA a c) (hB : IsPullback rB sB b c)
    (f' : A' ⟶ B') [IsIso f'] (hf₁ : f' ≫ rB = rA ≫ f) (hf₂ : f' ≫ sB = sA) :
    IsIso (pullback.map a c b c f (𝟙 S) (𝟙 S₀)
      ((Category.comp_id a).trans hf.symm) (by simp)) := by
  have he : pullback.map a c b c f (𝟙 S) (𝟙 S₀)
      ((Category.comp_id a).trans hf.symm) (by simp) =
      hA.isoPullback.inv ≫ f' ≫ hB.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pullback.map, pullback.lift_fst, Category.assoc, hB.isoPullback_hom_fst]
      rw [hf₁, ← Category.assoc, hA.isoPullback_inv_fst]
    · simp only [pullback.map, pullback.lift_snd, Category.assoc, hB.isoPullback_hom_snd]
      rw [hf₂, hA.isoPullback_inv_snd, Category.comp_id]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MapRealizationIso
