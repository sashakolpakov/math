import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FiniteEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Isomorphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms.Coefficients

/-! Generalization of the proved Isomorphisms construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Isomorphisms of generic fibers descend with their inverse identities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem isomorphism_between_models_descends
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s : Finset K}
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s))
    (hX₀ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X₀.hom)
    (hY₀ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : IsPullback pX X.hom X₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s))
    (hY : IsPullback pY Y.hom Y₀.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s))
    (e : X ≅ Y) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (e₀ : (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj X₀ ≅
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj Y₀),
      Morphisms.Coefficients.genericModelLift X₀ pX hX.w h ≫ e₀.hom.left =
        e.hom.left ≫ Morphisms.Coefficients.genericModelLift Y₀ pY hY.w h := by
  let Z : Bool → Over (Spec (CommRingCat.of K)) | false => X | true => Y
  let Z₀ : Bool → Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s) | false => X₀ | true => Y₀
  let p : ∀ i, (Z i).left ⟶ (Z₀ i).left | false => pX | true => pY
  have hZ₀ : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (Z₀ i).hom
    | false => hX₀ | true => hY₀
  have hp : ∀ i, IsPullback (p i) (Z i).hom (Z₀ i).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
    | false => hX | true => hY
  let a : ∀ i, Z i ⟶ Z (!i) | false => e.hom | true => e.inv
  obtain ⟨t, hst, b, hb⟩ := CommonStage.Coefficients.finite_morphisms_descend id Bool.not Z Z₀ hZ₀ p hp a
  let B := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K hst)
  let Z₁ : Bool → Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K t) := fun i ↦ B.obj (Z₀ i)
  let p₁ : ∀ i, (Z i).left ⟶ (Z₁ i).left :=
    fun i ↦ Morphisms.Coefficients.genericModelLift (Z₀ i) (p i) (hp i).w hst
  have hZ₁ : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (Z₁ i).hom :=
    fun i ↦ Finiteness.Coefficients.baseChange_finitePresentation _ _ (hZ₀ i)
  have hp₁ : ∀ i, IsPullback (p₁ i) (Z i).hom (Z₁ i).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t) :=
    fun i ↦ Morphisms.Coefficients.genericModelLift_cartesian (Z₀ i) (p i) (hp i) hst
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
  obtain ⟨z, htz, hz⟩ := FiniteEquations.Coefficients.finite_equations_descend id id Z Z₁ hZ₁ p₁ hp₁ c d hc
  let C := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K htz)
  let e₁ : C.obj (Z₁ false) ≅ C.obj (Z₁ true) :=
    { hom := C.map (b false)
      inv := C.map (b true)
      hom_inv_id := by
        rw [← C.map_comp]
        exact (hz false).trans (C.map_id _)
      inv_hom_id := by
        rw [← C.map_comp]
        exact (hz true).trans (C.map_id _) }
  let e₀ := (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz X₀).symm ≪≫ e₁ ≪≫
    BaseChange.Coefficients.coefficientBaseChangeTrans hst htz Y₀
  refine ⟨z, hst.trans htz, e₀, ?_⟩
  exact CommonStage.Coefficients.descendedMorphismAtLargerBase_compatibility X₀ Y₀ pX pY hX.w hY.w e.hom
    hst htz (b false) (hb false)

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms.Coefficients
