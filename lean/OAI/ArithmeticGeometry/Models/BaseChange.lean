import OAI.ArithmeticGeometry.Models.ModelMorphisms

/-! # Base Change -/

namespace OAI.ArithmeticGeometry.Models.BaseChange.Constructions.Foundations

/-! Compatibility of coefficient enlargement with model maps and morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

noncomputable def iteratedBaseChangeIso {S T U : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ T) (X : Over S) :
    (Over.pullback g).obj ((Over.pullback f).obj X) ≅
      (Over.pullback (g ≫ f)).obj X :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom f g)
    (pullbackLeftPullbackSndIso_hom_snd X.hom f g)

@[reassoc]
theorem baseChangeCongr_hom_fst {S T : Scheme.{u}} {f g : T ⟶ S}
    (h : f = g) (X : Over S) :
    (Models.Scheme.Constructions.Foundations.baseChangeCongr h X).hom.left ≫ pullback.fst X.hom g = pullback.fst X.hom f := by
  subst g
  exact Category.id_comp _

@[reassoc]
theorem baseChangeCongr_hom_snd {S T : Scheme.{u}} {f g : T ⟶ S}
    (h : f = g) (X : Over S) :
    (Models.Scheme.Constructions.Foundations.baseChangeCongr h X).hom.left ≫ pullback.snd X.hom g = pullback.snd X.hom f := by
  subst g
  exact Category.id_comp _

variable {K : Type u} [Field K] {s t v : Finset K}

theorem coefficientBaseChangeTransSquare
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    IsPullback
      (pullback.fst (pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
        (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htv) ≫
        pullback.fst X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
      (pullback.snd (pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
        (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htv))
      X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htv)) := by
  have H := (IsPullback.of_hasPullback
    (pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
    (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htv)).paste_horiz
      (IsPullback.of_hasPullback X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
  erw [CoefficientSystem.Constructions.Foundations.coefficientBaseMap_comp] at H
  exact H

noncomputable def coefficientBaseChangeTrans
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htv)).obj
        ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj X₀) ≅
      (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htv))).obj X₀ :=
  Over.isoMk (coefficientBaseChangeTransSquare hst htv X₀).isoPullback
    (coefficientBaseChangeTransSquare hst htv X₀).isoPullback_hom_snd

@[reassoc]
theorem coefficientBaseChangeTrans_hom_fst
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    (coefficientBaseChangeTrans hst htv X₀).hom.left ≫
        pullback.fst X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htv)) =
      pullback.fst (pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
        (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htv) ≫
        pullback.fst X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst) :=
  (coefficientBaseChangeTransSquare hst htv X₀).isoPullback_hom_fst

@[reassoc]
theorem coefficientBaseChangeTrans_hom_snd
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    (coefficientBaseChangeTrans hst htv X₀).hom.left ≫
        pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htv)) =
      pullback.snd (pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst))
        (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htv) :=
  (coefficientBaseChangeTrans hst htv X₀).hom.w

/-- Successive coefficient enlargement has the same generic map as direct enlargement. -/
theorem genericModelLift_trans
    {X : Over (Spec (CommRingCat.of K))}
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    (hst : s ⊆ t) (htv : t ⊆ v) :
    ModelMorphisms.Constructions.Foundations.genericModelLift ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).obj X₀)
        (ModelMorphisms.Constructions.Foundations.genericModelLift X₀ p hp hst) (ModelMorphisms.Constructions.Foundations.genericModelLift_snd X₀ p hp hst) htv ≫
        (coefficientBaseChangeTrans hst htv X₀).hom.left =
      ModelMorphisms.Constructions.Foundations.genericModelLift X₀ p hp (hst.trans htv) := by
  apply pullback.hom_ext (f := X₀.hom)
    (g := CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htv))
  · erw [Category.assoc, coefficientBaseChangeTrans_hom_fst, ← Category.assoc,
      ModelMorphisms.Constructions.Foundations.genericModelLift_fst, ModelMorphisms.Constructions.Foundations.genericModelLift_fst, ModelMorphisms.Constructions.Foundations.genericModelLift_fst]
  · erw [Category.assoc, coefficientBaseChangeTrans_hom_snd,
      ModelMorphisms.Constructions.Foundations.genericModelLift_snd, ModelMorphisms.Constructions.Foundations.genericModelLift_snd]

/-- Base change preserves the compatibility of a model morphism with its generic fiber. -/
theorem genericModelLift_map
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : pX ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    (hY : pY ≫ Y₀.hom = Y.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    (a : X ⟶ Y) (b : X₀ ⟶ Y₀) (hab : pX ≫ b.left = a.left ≫ pY) (hst : s ⊆ t) :
    ModelMorphisms.Constructions.Foundations.genericModelLift X₀ pX hX hst ≫
        ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).map b).left =
      a.left ≫ ModelMorphisms.Constructions.Foundations.genericModelLift Y₀ pY hY hst := by
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      ModelMorphisms.Constructions.Foundations.genericModelLift_fst, hab, Category.assoc, ModelMorphisms.Constructions.Foundations.genericModelLift_fst]
  · erw [Category.assoc, pullback.lift_snd, ModelMorphisms.Constructions.Foundations.genericModelLift_snd,
      Category.assoc, ModelMorphisms.Constructions.Foundations.genericModelLift_snd, ← Category.assoc, a.w]

end OAI.ArithmeticGeometry.Models.BaseChange.Constructions.Foundations
