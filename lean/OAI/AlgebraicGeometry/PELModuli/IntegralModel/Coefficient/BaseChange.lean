import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Morphisms

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.BaseChange.Coefficients

/-! Generalization of the proved BaseChange construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Compatibility of coefficient enlargement with model maps and morphisms. -/

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
    (ArithmeticGeometry.Models.Scheme.Constructions.Foundations.baseChangeCongr h X).hom.left ≫ pullback.fst X.hom g = pullback.fst X.hom f := by
  subst g
  exact Category.id_comp _

@[reassoc]
theorem baseChangeCongr_hom_snd {S T : Scheme.{u}} {f g : T ⟶ S}
    (h : f = g) (X : Over S) :
    (ArithmeticGeometry.Models.Scheme.Constructions.Foundations.baseChangeCongr h X).hom.left ≫ pullback.snd X.hom g = pullback.snd X.hom f := by
  subst g
  exact Category.id_comp _

variable {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t v : Finset K}

theorem coefficientBaseChangeTransSquare
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    IsPullback
      (pullback.fst (pullback.snd X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
        (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htv) ≫
        pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
      (pullback.snd (pullback.snd X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
        (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htv))
      X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htv)) := by
  have H := (IsPullback.of_hasPullback
    (pullback.snd X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htv)).paste_horiz
      (IsPullback.of_hasPullback X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
  erw [ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap_comp] at H
  exact H

noncomputable def coefficientBaseChangeTrans
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htv)).obj
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj X₀) ≅
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htv))).obj X₀ :=
  Over.isoMk (coefficientBaseChangeTransSquare hst htv X₀).isoPullback
    (coefficientBaseChangeTransSquare hst htv X₀).isoPullback_hom_snd

@[reassoc]
theorem coefficientBaseChangeTrans_hom_fst
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    (coefficientBaseChangeTrans hst htv X₀).hom.left ≫
        pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htv)) =
      pullback.fst (pullback.snd X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
        (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htv) ≫
        pullback.fst X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst) :=
  (coefficientBaseChangeTransSquare hst htv X₀).isoPullback_hom_fst

@[reassoc]
theorem coefficientBaseChangeTrans_hom_snd
    (hst : s ⊆ t) (htv : t ⊆ v) (X₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    (coefficientBaseChangeTrans hst htv X₀).hom.left ≫
        pullback.snd X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htv)) =
      pullback.snd (pullback.snd X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst))
        (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htv) :=
  (coefficientBaseChangeTrans hst htv X₀).hom.w

/-- Successive coefficient enlargement has the same generic map as direct enlargement. -/
theorem genericModelLift_trans
    {X : Over (Spec (CommRingCat.of K))}
    (X₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    (hst : s ⊆ t) (htv : t ⊆ v) :
    Morphisms.Coefficients.genericModelLift ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).obj X₀)
        (Morphisms.Coefficients.genericModelLift X₀ p hp hst) (Morphisms.Coefficients.genericModelLift_snd X₀ p hp hst) htv ≫
        (coefficientBaseChangeTrans hst htv X₀).hom.left =
      Morphisms.Coefficients.genericModelLift X₀ p hp (hst.trans htv) := by
  apply pullback.hom_ext (f := X₀.hom)
    (g := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K (hst.trans htv))
  · erw [Category.assoc, coefficientBaseChangeTrans_hom_fst, ← Category.assoc,
      Morphisms.Coefficients.genericModelLift_fst, Morphisms.Coefficients.genericModelLift_fst, Morphisms.Coefficients.genericModelLift_fst]
  · erw [Category.assoc, coefficientBaseChangeTrans_hom_snd,
      Morphisms.Coefficients.genericModelLift_snd, Morphisms.Coefficients.genericModelLift_snd]

/-- Base change preserves the compatibility of a model morphism with its generic fiber. -/
theorem genericModelLift_map
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s))
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : pX ≫ X₀.hom = X.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    (hY : pY ≫ Y₀.hom = Y.hom ≫ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    (a : X ⟶ Y) (b : X₀ ⟶ Y₀) (hab : pX ≫ b.left = a.left ≫ pY) (hst : s ⊆ t) :
    Morphisms.Coefficients.genericModelLift X₀ pX hX hst ≫
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)).map b).left =
      a.left ≫ Morphisms.Coefficients.genericModelLift Y₀ pY hY hst := by
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      Morphisms.Coefficients.genericModelLift_fst, hab, Category.assoc, Morphisms.Coefficients.genericModelLift_fst]
  · erw [Category.assoc, pullback.lift_snd, Morphisms.Coefficients.genericModelLift_snd,
      Category.assoc, Morphisms.Coefficients.genericModelLift_snd, ← Category.assoc, a.w]

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.BaseChange.Coefficients
