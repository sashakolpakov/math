import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Descent

/-! # Cover Proper Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverProperDescent

noncomputable section

/-! Separatedness and properness descend through a finite surjective
source cover. The proof uses the actual diagonal and its finite square map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem separated_of_finite_surjective_cover {X Y S : Scheme.{0}}
    (q : X ⟶ Y) (f : Y ⟶ S) [IsFinite q] [Surjective q]
    [IsSeparated (q ≫ f)] : IsSeparated f := by
  let m := pullback.map (q ≫ f) (q ≫ f) f f q q (𝟙 S) (by simp) (by simp)
  have : IsFinite m := MorphismProperty.pullbackMap
    (P := @IsFinite) (inferInstanceAs (IsFinite q)) (inferInstanceAs (IsFinite q)) rfl rfl
  have h : q ≫ pullback.diagonal f = pullback.diagonal (q ≫ f) ≫ m := by
    apply pullback.hom_ext
    · dsimp only [m, pullback.map]
      rw [Category.assoc, pullback.diagonal_fst, Category.comp_id,
        Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.diagonal_fst, Category.id_comp]
    · dsimp only [m, pullback.map]
      rw [Category.assoc, pullback.diagonal_snd, Category.comp_id,
        Category.assoc, pullback.lift_snd, ← Category.assoc,
        pullback.diagonal_snd, Category.id_comp]
  have : UniversallyClosed (q ≫ pullback.diagonal f) := by
    rw [h]
    infer_instance
  have : UniversallyClosed (pullback.diagonal f) :=
    UniversallyClosed.of_comp_surjective q (pullback.diagonal f)
  exact (Descent.separated_iff_diagonal_universallyClosed f).mpr this

theorem proper_of_finite_surjective_cover {X Y S : Scheme.{0}}
    (q : X ⟶ Y) (f : Y ⟶ S) [IsFinite q] [Surjective q]
    [IsProper (q ≫ f)] [LocallyOfFiniteType f] : IsProper f := by
  have : IsSeparated f := separated_of_finite_surjective_cover q f
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective q f
  exact ⟨⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverProperDescent
