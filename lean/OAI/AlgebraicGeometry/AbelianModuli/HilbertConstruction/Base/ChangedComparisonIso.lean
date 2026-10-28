import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.PullbackRecoveryIso

/-! # Changed Comparison Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedComparisonIso

noncomputable section

/-! Any Cartesian realization of a model comparison is an isomorphism when recovery is common. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]

theorem isIso_baseChanged_comparison_of_common_recovery
    {P A B S S₀ A' B' : C} (qA : P ⟶ A) (qB : P ⟶ B)
    (p : P ⟶ S) (a : A ⟶ S₀) (b : B ⟶ S₀) (c : S ⟶ S₀)
    (f : A ⟶ B) (hf : f ≫ b = a)
    [HasPullback a c] [HasPullback b c]
    (hA : IsPullback qA p a c) (hB : IsPullback qB p b c) (hq : qA ≫ f = qB)
    (rA : A' ⟶ A) (rB : B' ⟶ B) (sA : A' ⟶ S) (sB : B' ⟶ S)
    (hA' : IsPullback rA sA a c) (hB' : IsPullback rB sB b c)
    (f' : A' ⟶ B') (hf₁ : f' ≫ rB = rA ≫ f) (hf₂ : f' ≫ sB = sA) : IsIso f' := by
  let k := pullback.map a c b c f (𝟙 S) (𝟙 S₀)
    ((Category.comp_id a).trans hf.symm) (by simp)
  have : IsIso k := Common.PullbackRecoveryIso.isIso_pullback_map_of_common_recovery qA qB p a b c f hf hA hB hq
  have he : f' = hA'.isoPullback.hom ≫ k ≫ hB'.isoPullback.inv := by
    apply hB'.hom_ext
    · rw [Category.assoc, Category.assoc, hB'.isoPullback_inv_fst, hf₁]
      change rA ≫ f = hA'.isoPullback.hom ≫ (pullback.map a c b c f (𝟙 S) (𝟙 S₀) _ _ ≫ _)
      simp only [pullback.map, pullback.lift_fst, ← Category.assoc, hA'.isoPullback_hom_fst]
    · rw [Category.assoc, Category.assoc, hB'.isoPullback_inv_snd, hf₂]
      change sA = hA'.isoPullback.hom ≫ (pullback.map a c b c f (𝟙 S) (𝟙 S₀) _ _ ≫ _)
      simp only [pullback.map, pullback.lift_snd, Category.comp_id, hA'.isoPullback_hom_snd]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedComparisonIso
