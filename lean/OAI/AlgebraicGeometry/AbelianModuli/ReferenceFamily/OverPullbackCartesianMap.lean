import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Over Pullback Cartesian Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap

noncomputable section

section

/-! Base change in the category of schemes over a base retains
the actual open immersion underlying a morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem overPullback_map_open {B C : Scheme} (f : B ⟶ C)
    {X Y : Over C} (i : X ⟶ Y) [IsOpenImmersion i.left] :
    IsOpenImmersion (((Over.pullback f).map i).left) := by
  have h₁ : X.hom ≫ 𝟙 C = i.left ≫ Y.hom := (Category.comp_id _).trans i.w.symm
  have h₂ : f ≫ 𝟙 C = 𝟙 B ≫ f := (Category.comp_id _).trans (Category.id_comp _).symm
  have he : ((Over.pullback f).map i).left =
      pullback.map X.hom f Y.hom f i.left (𝟙 B) (𝟙 C) h₁ h₂ := by
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.map, pullback.lift_fst]
    · simp only [Over.pullback_map_left, pullback.map, pullback.lift_snd, Category.comp_id]
  rw [he]
  infer_instance

end

/-! The underlying naturality square of base change in an over
category is an actual scheme pullback square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem overPullback_map_isPullback {B C : Scheme} (f : B ⟶ C)
    {X Y : Over C} (i : X ⟶ Y) :
    IsPullback ((Over.pullback f).map i).left (pullback.fst X.hom f)
      (pullback.fst Y.hom f) i.left := by
  have ho : IsPullback (((Over.pullback f).map i).left ≫ pullback.snd Y.hom f)
      (pullback.fst X.hom f) f (i.left ≫ Y.hom) := by
    simp only [Over.pullback_map_left, pullback.lift_snd, i.w]
    exact (IsPullback.of_hasPullback X.hom f).flip
  have hc : ((Over.pullback f).map i).left ≫ pullback.fst Y.hom f =
      pullback.fst X.hom f ≫ i.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  exact ho.of_right hc (IsPullback.of_hasPullback Y.hom f).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap
