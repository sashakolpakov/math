import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionAdjunction

/-! # Reduction Frame Hom Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ReductionFrameHomEquiv

noncomputable section

/-! A frame identified with canonical reduction represents all maps from objects at the lower level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (U V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : B)}) (δ := δ) f n)
  (T : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f)
  (e : V ≅ (Crystalline.LevelReductionFunctor.functor n).obj T)

def equivalence : (U ⟶ V) ≃ (U.obj ⟶ T) :=
  (show (U ⟶ V) ≃ (U ⟶ (Crystalline.LevelReductionFunctor.functor n).obj T) from
    { toFun := fun a => a ≫ e.hom
      invFun := fun a => a ≫ e.inv
      left_inv := fun a => by simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
      right_inv := fun a => by simp only [Category.assoc, e.inv_hom_id, Category.comp_id] }).trans
    (Crystalline.LevelReductionAdjunction.homEquiv f n U T).symm

theorem equivalence_apply (a : U ⟶ V) : equivalence f n U V T e a =
    a.hom ≫ (e.hom.hom ≫ Crystalline.LevelReduction.hom n T) := by
  change (a.hom ≫ e.hom.hom) ≫ Crystalline.LevelReduction.hom n T = _
  exact Category.assoc _ _ _

theorem bijective (α : V.obj ⟶ T) (hα : e.hom.hom ≫ Crystalline.LevelReduction.hom n T = α) :
    Function.Bijective (fun a : U ⟶ V => a.hom ≫ α) := by
  have he : (fun a : U ⟶ V => a.hom ≫ α) = equivalence f n U V T e :=
    funext (fun a => (congrArg (fun b => a.hom ≫ b) hα).symm.trans (equivalence_apply f n U V T e a).symm)
  exact he ▸ (equivalence f n U V T e).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ReductionFrameHomEquiv
