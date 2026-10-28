import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothProperModel
import OAI.ArithmeticGeometry.Models.CommonStage

/-! # Finite -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Finite.Construction

noncomputable section

/-! Simultaneous smooth proper coefficient models for finite families and arrows. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

open OAI.ArithmeticGeometry.Models.CommonStage.Constructions.Foundations

theorem smooth_proper_has_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom] :
    ∃ M : Foundations.Constructions.CoefficientModel K X, Smooth M.model.hom ∧ IsProper M.model.hom := by
  obtain ⟨Z, f, hf, P, hP, ⟨e⟩⟩ := SmoothProperModel.Construction.smooth_proper_scheme_has_integral_cover K X
  have := hf
  have := hP
  obtain ⟨P₀, hP₀⟩ := Cover.Construction.proper_integral_model_as_coefficient_model P e
  have := hP₀
  obtain ⟨M, hM⟩ := CoverDescent.Construction.proper_model_of_cover
    (show Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom from ⟨inferInstance, inferInstance, inferInstance⟩)
    f P₀
  have := hM
  have : IsIso M.genericIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericIso.hom))
  have hs : Smooth (M.genericIso.hom.left ≫ X.hom) := inferInstance
  rw [M.genericIso.hom.w] at hs
  have := hs
  obtain ⟨t, h, hsm⟩ := CoefficientSmoothness.Construction.proper_coefficient_model_eventually_smooth M.model
  exact ⟨M.enlarge t h, hsm,
    inferInstanceAs (IsProper (pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)))⟩

theorem finite_smooth_proper_common_coefficient_base
    {K : Type u} [Field K] [NumberField K] {ι : Type v} [Finite ι]
    (X : ι → Over (Spec (.of K))) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) :
    ∃ (s : Finset K) (M : ι → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (p : ∀ i, (X i).left ⟶ (M i).left),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom) ∧
      (∀ i, IsPullback (p i) (X i).hom (M i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose M hM using fun i ↦ smooth_proper_has_coefficient_model (X i)
  let s := Finset.univ.biUnion (fun i ↦ (M i).coefficients)
  have h (i : ι) : (M i).coefficients ⊆ s :=
    Finset.subset_biUnion_of_mem (fun i ↦ (M i).coefficients) (Finset.mem_univ i)
  let N (i : ι) := (M i).enlarge s (h i)
  refine ⟨s, (fun i ↦ (N i).model), (fun i ↦ (N i).specialization), ?_,
    fun i ↦ (N i).cartesian⟩
  intro i
  have : Smooth (M i).model.hom := (hM i).1
  have : IsProper (M i).model.hom := (hM i).2
  exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).model.hom
    (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (h i)))),
    inferInstanceAs (IsProper (pullback.snd (M i).model.hom
      (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (h i))))⟩

theorem finite_smooth_proper_arrows_coefficient_model
    {K : Type u} [Field K] [NumberField K] {ι : Type v} {α : Type w}
    [Finite ι] [Finite α]
    (X : ι → Over (Spec (.of K))) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (src dst : α → ι)
    (f : ∀ a, X (src a) ⟶ X (dst a)) :
    ∃ (s : Finset K) (M : ι → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (p : ∀ i, (X i).left ⟶ (M i).left) (fM : ∀ a, M (src a) ⟶ M (dst a)),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom) ∧
      (∀ i, IsPullback (p i) (X i).hom (M i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) ∧
      (∀ a, p (src a) ≫ (fM a).left = (f a).left ≫ p (dst a)) := by
  obtain ⟨s, M, p, hM, hcart⟩ := finite_smooth_proper_common_coefficient_base X hs hp
  have hFP (i : ι) : Scheme.Constructions.Foundations.FinitePresentationMorphism (M i).hom := by
    have := (hM i).1
    have := (hM i).2
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, h, fM, hfM⟩ := CommonStage.Constructions.Foundations.finite_morphisms_descend src dst X M hFP p hcart f
  refine ⟨t, (fun i ↦ (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj (M i)),
    (fun i ↦ ModelMorphisms.Constructions.Foundations.genericModelLift (M i) (p i) (hcart i).w h), fM, ?_, ?_, hfM⟩
  · intro i
    have := (hM i).1
    have := (hM i).2
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom _)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom _))⟩
  · intro i
    exact ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian (M i) (p i) (hcart i) h

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Finite.Construction
