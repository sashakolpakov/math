import OAI.ArithmeticGeometry.Models.CommonStage
import OAI.ArithmeticGeometry.Models.FiniteEquations
import OAI.ArithmeticGeometry.Models.ModelFiniteness

/-! # Isomorphisms -/

namespace OAI.ArithmeticGeometry.Models.Isomorphisms.Constructions.Foundations

/-! Isomorphisms of generic fibers descend with their inverse identities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem isomorphism_between_models_descends
    {K : Type u} [Field K] {s : Finset K}
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism X₀.hom)
    (hY₀ : Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : IsPullback pX X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (hY : IsPullback pY Y.hom Y₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (e : X ≅ Y) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (e₀ : (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj X₀ ≅
        (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj Y₀),
      ModelMorphisms.Constructions.Foundations.genericModelLift X₀ pX hX.w h ≫ e₀.hom.left =
        e.hom.left ≫ ModelMorphisms.Constructions.Foundations.genericModelLift Y₀ pY hY.w h := by
  let Z : Bool → Over (Spec (CommRingCat.of K)) | false => X | true => Y
  let Z₀ : Bool → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s) | false => X₀ | true => Y₀
  let p : ∀ i, (Z i).left ⟶ (Z₀ i).left | false => pX | true => pY
  have hZ₀ : ∀ i, Scheme.Constructions.Foundations.FinitePresentationMorphism (Z₀ i).hom
    | false => hX₀ | true => hY₀
  have hp : ∀ i, IsPullback (p i) (Z i).hom (Z₀ i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
    | false => hX | true => hY
  let a : ∀ i, Z i ⟶ Z (!i) | false => e.hom | true => e.inv
  obtain ⟨t, hst, b, hb⟩ := CommonStage.Constructions.Foundations.finite_morphisms_descend id Bool.not Z Z₀ hZ₀ p hp a
  let B := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)
  let Z₁ : Bool → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K t) := fun i ↦ B.obj (Z₀ i)
  let p₁ : ∀ i, (Z i).left ⟶ (Z₁ i).left :=
    fun i ↦ ModelMorphisms.Constructions.Foundations.genericModelLift (Z₀ i) (p i) (hp i).w hst
  have hZ₁ : ∀ i, Scheme.Constructions.Foundations.FinitePresentationMorphism (Z₁ i).hom :=
    fun i ↦ ModelFiniteness.Constructions.Foundations.baseChange_finitePresentation _ _ (hZ₀ i)
  have hp₁ : ∀ i, IsPullback (p₁ i) (Z i).hom (Z₁ i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t) :=
    fun i ↦ ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian (Z₀ i) (p i) (hp i) hst
  let c : ∀ i, Z₁ i ⟶ Z₁ i
    | false => b false ≫ b true
    | true => b true ≫ b false
  let d : ∀ i, Z₁ i ⟶ Z₁ i := fun i ↦ 𝟙 _
  have hc : ∀ i, p₁ i ≫ (c i).left = p₁ i ≫ (d i).left := by
    intro i
    cases i
    · change p₁ false ≫ ((b false).left ≫ (b true).left) = p₁ false ≫ 𝟙 _
      erw [← Category.assoc, hb false, Category.assoc, hb true,
        ← Category.assoc, Over.hom_left_inv_left, Category.id_comp]
    · change p₁ true ≫ ((b true).left ≫ (b false).left) = p₁ true ≫ 𝟙 _
      erw [← Category.assoc, hb true, Category.assoc, hb false,
        ← Category.assoc, Over.inv_left_hom_left, Category.id_comp]
  obtain ⟨z, htz, hz⟩ := FiniteEquations.Constructions.Foundations.finite_equations_descend id id Z Z₁ hZ₁ p₁ hp₁ c d hc
  let C := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htz)
  let e₁ : C.obj (Z₁ false) ≅ C.obj (Z₁ true) :=
    { hom := C.map (b false)
      inv := C.map (b true)
      hom_inv_id := by
        rw [← C.map_comp]
        exact (hz false).trans (C.map_id _)
      inv_hom_id := by
        rw [← C.map_comp]
        exact (hz true).trans (C.map_id _) }
  let e₀ := (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X₀).symm ≪≫ e₁ ≪≫
    BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz Y₀
  refine ⟨z, hst.trans htz, e₀, ?_⟩
  exact CommonStage.Constructions.Foundations.descendedMorphismAtLargerBase_compatibility X₀ Y₀ pX pY hX.w hY.w e.hom
    hst htz (b false) (hb false)

end OAI.ArithmeticGeometry.Models.Isomorphisms.Constructions.Foundations
