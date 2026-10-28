import OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersion
import OAI.ArithmeticGeometry.Models.Isomorphisms
import OAI.ArithmeticGeometry.Models.FoundationsPullback

/-! # Closed Immersion Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersionDescent.Construction

noncomputable section

/-! A closed immersion on generic fibers is a closed immersion after a
finite enlargement of the coefficients of its existing models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem baseChange_closedImmersion
    {S T : Scheme.{u}} (g : T ⟶ S) {X Y : Over S} (f : X ⟶ Y)
    [IsClosedImmersion f.left] :
    IsClosedImmersion ((Over.pullback g).map f).left :=
  MorphismProperty.of_isPullback (FoundationsPullback.Constructions.pullback_over_map_isPullback g f).flip inferInstance

/-- The two orders of coefficient enlargement respect every model arrow. -/
theorem coefficientBaseChangeTrans_map
    {K : Type u} [Field K] {s t z : Finset K}
    (hst : s ⊆ t) (htz : t ⊆ z)
    {X Y : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)} (f : X ⟶ Y) :
    ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htz)).map
      ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)).map f)).left ≫
        (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz Y).hom.left =
      (BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X).hom.left ≫
        ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (hst.trans htz))).map f).left := by
  apply pullback.hom_ext
  · erw [Category.assoc, BaseChange.Constructions.Foundations.coefficientBaseChangeTrans_hom_fst,
      ← Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst,
      Category.assoc, pullback.lift_fst,
      BaseChange.Constructions.Foundations.coefficientBaseChangeTrans_hom_fst_assoc]
    rfl
  · erw [Category.assoc, BaseChange.Constructions.Foundations.coefficientBaseChangeTrans_hom_snd,
      pullback.lift_snd, Category.assoc, pullback.lift_snd,
      BaseChange.Constructions.Foundations.coefficientBaseChangeTrans_hom_snd]
    rfl

theorem closed_immersion_eventually_on_models
    {K : Type u} [Field K] [NumberField K] {s : Finset K}
    {X Y : Over (Spec (CommRingCat.of K))}
    (X₀ Y₀ : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hX₀ : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X₀.hom)
    (hY₀ : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom)
    (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : IsPullback pX X.hom X₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (hY : IsPullback pY Y.hom Y₀.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
    (i : X ⟶ Y) [IsClosedImmersion i.left] (a : X₀ ⟶ Y₀)
    (ha : pX ≫ a.left = i.left ≫ pY) :
    ∃ (t : Finset K) (h : s ⊆ t),
      IsClosedImmersion ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).map a).left := by
  let MY := Foundations.Constructions.CoefficientModel.ofCartesian s Y₀ hY₀ pY hY
  obtain ⟨Z₀, j, pZ, hZ₀, hj, hZ, hcompat⟩ := ClosedImmersion.Construction.closed_immersion_has_model i MY
  have := hj
  have hpj : pZ ≫ j.left = i.left ≫ pY := by
    have hspec : MY.specialization = pY := Foundations.Constructions.CoefficientModel.ofCartesian_specialization
      s Y₀ hY₀ pY hY
    exact hcompat.trans (congrArg (fun q ↦ i.left ≫ q) hspec)
  obtain ⟨t, hst, e, he⟩ := Isomorphisms.Constructions.Foundations.isomorphism_between_models_descends
    X₀ Z₀ hX₀ hZ₀ pX pZ hX hZ (Iso.refl X)
  let B := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K hst)
  let b : B.obj X₀ ⟶ B.obj Y₀ := e.hom ≫ B.map j
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsClosedImmersion (B.map j).left := baseChange_closedImmersion _ j
  have hb : IsClosedImmersion b.left := by
    change IsClosedImmersion (e.hom.left ≫ (B.map j).left)
    infer_instance
  let qX := ModelMorphisms.Constructions.Foundations.genericModelLift X₀ pX hX.w hst
  have hqX := ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian X₀ pX hX hst
  have he' : qX ≫ e.hom.left = ModelMorphisms.Constructions.Foundations.genericModelLift Z₀ pZ hZ.w hst :=
    he.trans (Category.id_comp _)
  have hab : qX ≫ (B.map a).left = qX ≫ b.left := by
    change qX ≫ (B.map a).left = qX ≫ (e.hom.left ≫ (B.map j).left)
    rw [← Category.assoc, he']
    exact (BaseChange.Constructions.Foundations.genericModelLift_map X₀ Y₀ pX pY hX.w hY.w i a ha hst).trans
      (BaseChange.Constructions.Foundations.genericModelLift_map Z₀ Y₀ pZ pY hZ.w hY.w i j hpj hst).symm
  obtain ⟨z, htz, heq⟩ := ModelMorphisms.Constructions.Foundations.equation_between_models_descends
    (B.obj X₀) (B.obj Y₀)
    (ModelFiniteness.Constructions.Foundations.baseChange_finitePresentation _ _ hX₀) (ModelFiniteness.Constructions.Foundations.baseChange_finitePresentation _ _ hY₀)
    qX hqX (B.map a) b hab
  let C := Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htz)
  have heq' : C.map (B.map a) = C.map b :=
    FiniteEquations.Constructions.Foundations.baseChange_map_eq_of_fst_eq htz _ _ _ _ heq
  have : IsClosedImmersion (C.map (B.map a)).left := by
    rw [heq']
    exact baseChange_closedImmersion _ b
  let eX := BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz X₀
  let eY := BaseChange.Constructions.Foundations.coefficientBaseChangeTrans hst htz Y₀
  have : IsIso eX.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eX.hom))
  have : IsIso eY.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eY.hom))
  have hclosed : IsClosedImmersion ((C.map (B.map a)).left ≫ eY.hom.left) :=
    inferInstance
  rw [coefficientBaseChangeTrans_map hst htz a] at hclosed
  refine ⟨z, hst.trans htz, ?_⟩
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion eX.hom.left _).mp
    hclosed

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersionDescent.Construction
