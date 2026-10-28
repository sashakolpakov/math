import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison

/-! # Pullback Recovery Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.PullbackRecoveryIso

noncomputable section

/-! A map between two models of the same recovered object becomes an isomorphism after base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C]

theorem isIso_pullback_map_of_common_recovery
    {P A B S S₀ : C} (qA : P ⟶ A) (qB : P ⟶ B)
    (p : P ⟶ S) (a : A ⟶ S₀) (b : B ⟶ S₀) (c : S ⟶ S₀)
    (f : A ⟶ B) (hf : f ≫ b = a)
    [HasPullback a c] [HasPullback b c]
    (hA : IsPullback qA p a c) (hB : IsPullback qB p b c) (hq : qA ≫ f = qB) :
    IsIso (pullback.map a c b c f (𝟙 S) (𝟙 S₀)
      ((Category.comp_id a).trans hf.symm) (by simp)) := by
  let e := hA.isoPullback.symm ≪≫ hB.isoPullback
  have he : pullback.map a c b c f (𝟙 S) (𝟙 S₀)
      ((Category.comp_id a).trans hf.symm) (by simp) = e.hom := by
    apply pullback.hom_ext
    · change _ = (hA.isoPullback.inv ≫ hB.isoPullback.hom) ≫ pullback.fst b c
      simp only [pullback.map, pullback.lift_fst, Category.assoc, hB.isoPullback_hom_fst]
      rw [← hq, ← Category.assoc, hA.isoPullback_inv_fst]
    · change _ = (hA.isoPullback.inv ≫ hB.isoPullback.hom) ≫ pullback.snd b c
      simp only [pullback.map, pullback.lift_snd, Category.comp_id, Category.assoc,
        hB.isoPullback_hom_snd, hA.isoPullback_inv_snd]
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.PullbackRecoveryIso
