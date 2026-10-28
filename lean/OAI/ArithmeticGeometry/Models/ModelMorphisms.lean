import OAI.ArithmeticGeometry.Models.Descent

/-! # Model Morphisms -/

namespace OAI.ArithmeticGeometry.Models.ModelMorphisms.Constructions.Foundations

/-! Descent of morphisms between schemes with specified coefficient models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.NumberField

universe u

variable {K : Type u} [Field K]
variable {s t : Finset K} {X : Over (Spec (CommRingCat.of K))}

/-- The generic-fiber map into a base-changed model. -/
noncomputable def genericModelLift
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) (h : s ⊆ t) :
    X.left ⟶ ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj X₀).left :=
  pullback.lift p (X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t) (by
    erw [hp, Category.assoc, CoefficientSystem.Constructions.Foundations.genericBaseMap_comp])

@[reassoc]
theorem genericModelLift_fst
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) (h : s ⊆ t) :
    genericModelLift X₀ p hp h ≫ pullback.fst X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) = p :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem genericModelLift_snd
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : p ≫ X₀.hom = X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) (h : s ⊆ t) :
    genericModelLift X₀ p hp h ≫ pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) =
      X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t :=
  pullback.lift_snd _ _ _

theorem genericModelLift_cartesian
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : IsPullback p X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) (h : s ⊆ t) :
    IsPullback (genericModelLift X₀ p hp.w h) X.hom
      ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj X₀).hom
      (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t) := by
  apply IsPullback.of_right ?_ (genericModelLift_snd X₀ p hp.w h)
    (IsPullback.of_hasPullback X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h))
  erw [genericModelLift_fst, CoefficientSystem.Constructions.Foundations.genericBaseMap_comp]
  exact hp

/-- Relate the two orders of pullback used by canonical base change and the limit cone. -/
theorem genericModelLift_to_expansion
    (X₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) (p : X.left ⟶ X₀.left)
    (hp : IsPullback p X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (i : Over (op s)) :
    genericModelLift X₀ p hp.w (leOfHom i.hom.unop) ≫
        (pullbackSymmetry X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (leOfHom i.hom.unop))).hom =
      hp.flip.isoPullback.hom ≫ (Descent.Constructions.Foundations.expansionCone (𝓞 K) K s X₀).π.app i := by
  apply pullback.hom_ext
  · erw [Category.assoc, pullbackSymmetry_hom_comp_fst, genericModelLift_snd]
    change X.hom ≫ CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K i.left.unop =
      hp.flip.isoPullback.hom ≫
        (pullback.lift _ _ _ ≫ pullback.fst _ _)
    erw [pullback.lift_fst, ← Category.assoc, hp.flip.isoPullback_hom_fst]
    rfl
  · erw [Category.assoc, pullbackSymmetry_hom_comp_snd, genericModelLift_fst]
    change p = hp.flip.isoPullback.hom ≫
      (pullback.lift _ _ _ ≫ pullback.snd _ _)
    erw [pullback.lift_snd, hp.flip.isoPullback_hom_snd]

/-- Extend a generic morphism to a larger model of its source, keeping the
map to the original target model. -/
theorem morphism_to_model_descends
    {Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism X₀.hom)
    (hY₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : IsPullback pX X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (hY : IsPullback pY Y.hom Y₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (a : X ⟶ Y) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj X₀).left ⟶ Y₀.left),
      genericModelLift X₀ pX hX.w h ≫ b = a.left ≫ pY ∧
      b ≫ Y₀.hom = pullback.snd X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) ≫
        CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h := by
  let : QuasiCompact X₀.hom := hX₀.2.1
  let : QuasiSeparated X₀.hom := hX₀.2.2
  let : LocallyOfFinitePresentation Y₀.hom := hY₀.1
  let e : X.left ≅ (Descent.Constructions.Foundations.expansionCone (𝓞 K) K s X₀).pt := hX.flip.isoPullback
  let a₀ := e.inv ≫ a.left ≫ pY
  have ha₀ : a₀ ≫ Y₀.hom = (Descent.Constructions.Foundations.expansionOverCone (𝓞 K) K s X₀).pt.hom ≫ X₀.hom := by
    dsimp [a₀]
    erw [Category.assoc, Category.assoc, hY.w, ← Category.assoc a.left, a.w,
      ← Category.assoc, hX.flip.isoPullback_inv_fst]
    exact pullback.condition
  obtain ⟨i, g, hg, hgbase⟩ := Descent.Constructions.Foundations.generic_morphism_descends (𝓞 K) K s X₀ Y₀ a₀ ha₀
  let h : s ⊆ i.left.unop := leOfHom i.hom.unop
  let σ := pullbackSymmetry X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
  refine ⟨i.left.unop, h, σ.hom ≫ g, ?_, ?_⟩
  · erw [← Category.assoc, genericModelLift_to_expansion X₀ pX hX i, Category.assoc, hg]
    change e.hom ≫ e.inv ≫ a.left ≫ pY = a.left ≫ pY
    erw [Iso.hom_inv_id_assoc]
  · erw [Category.assoc, hgbase]
    change σ.hom ≫ pullback.snd _ X₀.hom ≫ X₀.hom =
      pullback.snd X₀.hom _ ≫ CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h
    erw [← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback.condition

/-- Both source and target may be enlarged together so the descended morphism
is a morphism over one common finite coefficient ring. -/
theorem morphism_between_models_descends
    {Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism X₀.hom)
    (hY₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : IsPullback pX X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (hY : IsPullback pY Y.hom Y₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (a : X ⟶ Y) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj X₀ ⟶
        (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj Y₀),
      genericModelLift X₀ pX hX.w h ≫ b.left =
        a.left ≫ genericModelLift Y₀ pY hY.w h := by
  obtain ⟨t, h, b, hb, hbbase⟩ :=
    morphism_to_model_descends X₀ Y₀ hX₀ hY₀ pX pY hX hY a
  let f := CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h
  let b' : (Over.pullback f).obj X₀ ⟶ (Over.pullback f).obj Y₀ :=
    Over.homMk (pullback.lift b (pullback.snd X₀.hom f) hbbase)
    (pullback.lift_snd b (pullback.snd X₀.hom f) hbbase)
  refine ⟨t, h, b', ?_⟩
  apply pullback.hom_ext
  · change genericModelLift X₀ pX hX.w h ≫ b'.left ≫ pullback.fst Y₀.hom f =
      (a.left ≫ genericModelLift Y₀ pY hY.w h) ≫ pullback.fst Y₀.hom f
    erw [pullback.lift_fst, hb, Category.assoc, genericModelLift_fst]
  · change genericModelLift X₀ pX hX.w h ≫ b'.left ≫ pullback.snd Y₀.hom f =
      (a.left ≫ genericModelLift Y₀ pY hY.w h) ≫ pullback.snd Y₀.hom f
    erw [pullback.lift_snd, genericModelLift_snd, Category.assoc,
      genericModelLift_snd, ← Category.assoc, a.w]

/-- An equality of two model morphisms that holds on the generic fiber holds
after a further common enlargement of the coefficient ring. -/
theorem equation_between_models_descends
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism X₀.hom)
    (hY₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (p : X.left ⟶ X₀.left)
    (hp : IsPullback p X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (a b : X₀ ⟶ Y₀) (hab : p ≫ a.left = p ≫ b.left) :
    ∃ (t : Finset K) (h : s ⊆ t),
      pullback.fst X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) ≫ a.left =
        pullback.fst X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) ≫ b.left := by
  let : QuasiCompact X₀.hom := hX₀.2.1
  let : LocallyOfFinitePresentation Y₀.hom := hY₀.1
  let i : Over (op s) := Over.mk (𝟙 (op s))
  let q := ((Descent.Constructions.Foundations.expansionOverDiagram (𝓞 K) K s X₀).obj i).hom
  have ha : (Descent.Constructions.Foundations.expansionToBase (𝓞 K) K s X₀).app i = (q ≫ a.left) ≫ Y₀.hom := by
    change q ≫ X₀.hom = (q ≫ a.left) ≫ Y₀.hom
    rw [Category.assoc, a.w]
  have hb : (Descent.Constructions.Foundations.expansionToBase (𝓞 K) K s X₀).app i = (q ≫ b.left) ≫ Y₀.hom := by
    change q ≫ X₀.hom = (q ≫ b.left) ≫ Y₀.hom
    rw [Category.assoc, b.w]
  have hc : (Descent.Constructions.Foundations.expansionCone (𝓞 K) K s X₀).π.app i ≫ (q ≫ a.left) =
      (Descent.Constructions.Foundations.expansionCone (𝓞 K) K s X₀).π.app i ≫ (q ≫ b.left) := by
    have H := congrArg (fun z ↦ hp.flip.isoPullback.inv ≫ z) hab
    erw [← Category.assoc, hp.flip.isoPullback_inv_snd,
      ← Category.assoc, hp.flip.isoPullback_inv_snd] at H
    erw [← Category.assoc, ((Descent.Constructions.Foundations.expansionOverCone (𝓞 K) K s X₀).π.app i).w,
      ← Category.assoc, ((Descent.Constructions.Foundations.expansionOverCone (𝓞 K) K s X₀).π.app i).w]
    exact H
  obtain ⟨j, hji, hj⟩ := Descent.Constructions.Foundations.generic_equation_descends (𝓞 K) K s X₀ Y₀ (q ≫ a.left) (q ≫ b.left)
    ha hb hc
  have H : ((Descent.Constructions.Foundations.expansionOverDiagram (𝓞 K) K s X₀).obj j).hom ≫ a.left =
      ((Descent.Constructions.Foundations.expansionOverDiagram (𝓞 K) K s X₀).obj j).hom ≫ b.left := by
    erw [← Category.assoc, ((Descent.Constructions.Foundations.expansionOverDiagram (𝓞 K) K s X₀).map hji).w,
      ← Category.assoc, ((Descent.Constructions.Foundations.expansionOverDiagram (𝓞 K) K s X₀).map hji).w] at hj
    exact hj
  let h : s ⊆ j.left.unop := leOfHom j.hom.unop
  refine ⟨j.left.unop, h, ?_⟩
  have H' := congrArg (fun z ↦ (pullbackSymmetry X₀.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).hom ≫ z) H
  erw [← Category.assoc, pullbackSymmetry_hom_comp_snd,
    ← Category.assoc, pullbackSymmetry_hom_comp_snd] at H'
  exact H'

end OAI.ArithmeticGeometry.Models.ModelMorphisms.Constructions.Foundations
