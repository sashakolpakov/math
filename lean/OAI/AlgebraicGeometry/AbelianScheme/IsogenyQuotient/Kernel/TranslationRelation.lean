import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Epi

/-! # Translation Relation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.TranslationRelation.Construction

noncomputable section

/-! The full all-test kernel condition identifies the actual kernel
pair with the translation relation, before choosing a quotient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

theorem kernel_translation_isKernelPair
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {A B H : C} [GrpObj A] [GrpObj B]
    (i : H ⟶ A) [Mono i] (q : A ⟶ B) [IsMonHom q]
    (hker : ∀ (T : C) (a : T ⟶ A),
      a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) :
    IsKernelPair q (snd H A) (Quotients.FiniteDescent.Epi.Construction.translation i) := by
  have hw : snd H A ≫ q = Quotients.FiniteDescent.Epi.Construction.translation i ≫ q := by
    rw [Quotients.FiniteDescent.Epi.Construction.translation, MonObj.mul_comp,
      Quotients.FiniteDescent.Epi.Construction.subgroup_point_comp_eq_one i q hker, one_mul]
  have hl (c : PullbackCone q q) : ∃! z : c.pt ⟶ H, (z ≫ i) * c.fst = c.snd :=
    (Quotients.FiniteDescent.Epi.Construction.same_image_iff_unique_translate i q hker c.pt c.snd c.fst).mp c.condition.symm
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk _ (fun c => lift (hl c).choose c.fst) ?_ ?_ ?_
  · intro c
    exact lift_snd _ _
  · intro c
    simpa only [Quotients.FiniteDescent.Epi.Construction.translation, MonObj.comp_mul, lift_fst_assoc, lift_snd] using
      (hl c).choose_spec.1
  · intro c m hm₁ hm₂
    apply hom_ext
    · rw [lift_fst]
      apply (hl c).choose_spec.2
      simpa only [Quotients.FiniteDescent.Epi.Construction.translation, MonObj.comp_mul, ← Category.assoc, hm₁] using hm₂
    · exact hm₁.trans (lift_snd _ _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.TranslationRelation.Construction
