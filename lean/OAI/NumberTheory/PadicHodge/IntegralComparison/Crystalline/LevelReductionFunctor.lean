import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction

/-! # Level Reduction Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionFunctor

noncomputable section

/-! Canonical prime-power reduction is a functor on the original crystalline objects. -/

open _root_.CategoryTheory

open _root_.AlgebraicGeometry OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (n : ℕ)

instance hom_mono (U : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f) : Mono (LevelReduction.hom n U) where
  right_cancellation {Z} a b h := by
    apply BigCrystallineSite.Object.Hom.ext
    apply DFunLike.ext
    intro y
    obtain ⟨x, rfl⟩ := LevelReduction.hom_surjective n U y
    exact congrArg (fun a : Z ⟶ U => a.ringMap x) h

def map {U V : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f} (α : U ⟶ V) : LevelReduction.object n U ⟶ LevelReduction.object n V :=
  LevelReduction.factor n (LevelReduction.hom n U ≫ α) (LevelReduction.prime_power_zero n U)

theorem map_comp_hom {U V : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f} (α : U ⟶ V) :
    LevelReductionFunctor.map n α ≫ LevelReduction.hom n V = LevelReduction.hom n U ≫ α :=
  LevelReduction.factor_comp n (LevelReduction.hom n U ≫ α) (LevelReduction.prime_power_zero n U)

theorem map_id (U : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f) : LevelReductionFunctor.map n (𝟙 U) = 𝟙 (LevelReduction.object n U) := by
  apply (cancel_mono (LevelReduction.hom n U)).mp
  rw [map_comp_hom, Category.comp_id, Category.id_comp]

theorem map_comp {U V W : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f} (α : U ⟶ V) (β : V ⟶ W) :
    LevelReductionFunctor.map n (α ≫ β) = LevelReductionFunctor.map n α ≫ LevelReductionFunctor.map n β := by
  apply (cancel_mono (LevelReduction.hom n W)).mp
  have h : (LevelReductionFunctor.map n α ≫ LevelReductionFunctor.map n β) ≫ LevelReduction.hom n W = LevelReduction.hom n U ≫ (α ≫ β) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun a => LevelReductionFunctor.map n α ≫ a) (map_comp_hom n β)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ β) (map_comp_hom n α)).trans (Category.assoc _ _ _))))
  exact (map_comp_hom n (α ≫ β)).trans h.symm

def functor : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f ⥤
    BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : B)}) (δ := δ) f n where
  obj U := LevelReduction.boundedObject n U
  map α := ObjectProperty.homMk (LevelReductionFunctor.map n α)
  map_id U := by
    apply (BoundedCrystalline.Site.inclusion f n).map_injective
    exact LevelReductionFunctor.map_id n U
  map_comp α β := by
    apply (BoundedCrystalline.Site.inclusion f n).map_injective
    exact LevelReductionFunctor.map_comp n α β

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionFunctor
