import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionFunctor

/-! # Level Reduction Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionAdjunction

noncomputable section

/-! Actual prime-power reduction is right adjoint to the original bounded-site inclusion, so it preserves products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReduction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {δ : DividedPowers (Ideal.span {(p : B)})}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def homEquiv (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : B)}) (δ := δ) f n)
    (V : BigCrystallineSite.Object p B (Ideal.span {(p : B)}) δ f) :
    (U.obj ⟶ V) ≃ (U ⟶ (LevelReductionFunctor.functor n).obj V) where
  toFun α := ObjectProperty.homMk (LevelReduction.factor n α U.property)
  invFun β := β.hom ≫ LevelReduction.hom n V
  left_inv α := LevelReduction.factor_comp n α U.property
  right_inv β := by
    apply (BoundedCrystalline.Site.inclusion f n).map_injective
    apply (cancel_mono (LevelReduction.hom n V)).mp
    exact LevelReduction.factor_comp n (β.hom ≫ LevelReduction.hom n V) U.property

def adjunction : BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : B)}) (δ := δ) f n ⊣
    LevelReductionFunctor.functor n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := LevelReductionAdjunction.homEquiv f n
      homEquiv_naturality_left_symm := by
        intro U V T α β
        exact Category.assoc α.hom β.hom (LevelReduction.hom n T)
      homEquiv_naturality_right := by
        intro U V W α β
        apply (BoundedCrystalline.Site.inclusion f n).map_injective
        apply (cancel_mono (LevelReduction.hom n W)).mp
        change LevelReduction.factor n (α ≫ β) U.property ≫ LevelReduction.hom n W =
          (LevelReduction.factor n α U.property ≫ LevelReductionFunctor.map n β) ≫ LevelReduction.hom n W
        exact (LevelReduction.factor_comp n (α ≫ β) U.property).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun a => LevelReduction.factor n α U.property ≫ a)
              (LevelReductionFunctor.map_comp_hom n β)).trans
                ((Category.assoc _ _ _).symm.trans
                  (congrArg (fun a => a ≫ β) (LevelReduction.factor_comp n α U.property))))).symm }

instance rightAdjoint : (LevelReductionFunctor.functor (p := p) (δ := δ) (f := f) n).IsRightAdjoint :=
  (adjunction f n).isRightAdjoint

instance preservesLimits : PreservesLimits (LevelReductionFunctor.functor (p := p) (δ := δ) (f := f) n) :=
  inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LevelReductionAdjunction
