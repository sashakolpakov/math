import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitConnected
import OAI.ArithmeticGeometry.Models.CommonStage

/-! # Split Finite -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitFinite.Construction

noncomputable section

/-! Simultaneous smooth proper split models and specified arrows, preserving
geometric connectedness wherever it holds on the generic object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

open OAI.ArithmeticGeometry.Models.CommonStage.Constructions.Foundations

theorem finite_split_models_common_base
    {K : Type u} [Field K] [NumberField K] {ι : Type v} [Finite ι]
    (X : ι → Over (Spec (.of K))) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (hX : ∀ i, Base.Construction.HasSplitGeometricComponents (X i)) :
    ∃ (s : Finset K) (M : ι → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (p : ∀ i, (X i).left ⟶ (M i).left),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom ∧ Base.Construction.HasSplitGeometricComponents (M i)) ∧
      (∀ i, IsPullback (p i) (X i).hom (M i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) ∧
      (∀ i, GeometricallyConnected (X i).hom → GeometricallyConnected (M i).hom) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose M hM using fun i ↦ SplitConnected.Construction.split_connected_smooth_proper_has_coefficient_model (X i) (hX i)
  let s := Finset.univ.biUnion (fun i ↦ (M i).coefficients)
  have h (i : ι) : (M i).coefficients ⊆ s :=
    Finset.subset_biUnion_of_mem (fun i ↦ (M i).coefficients) (Finset.mem_univ i)
  let N (i : ι) := (M i).enlarge s (h i)
  refine ⟨s, (fun i ↦ (N i).model), (fun i ↦ (N i).specialization), ?_,
    (fun i ↦ (N i).cartesian), ?_⟩
  · intro i
    have : Smooth (M i).model.hom := (hM i).1
    have : IsProper (M i).model.hom := (hM i).2.1
    exact ⟨OpenModel.Construction.coefficient_enlarge_smooth (M i) s (h i),
      OpenModel.Construction.coefficient_enlarge_proper (M i) s (h i),
      SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_baseChange (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (h i))
        (M i).model (hM i).2.2.1⟩
  · intro i hc
    have : GeometricallyConnected (M i).model.hom := (hM i).2.2.2 hc
    exact OpenModel.Construction.coefficient_enlarge_geometricallyConnected (M i) s (h i)

theorem finite_split_arrows_coefficient_model
    {K : Type u} [Field K] [NumberField K] {ι : Type v} {α : Type w}
    [Finite ι] [Finite α]
    (X : ι → Over (Spec (.of K))) (hs : ∀ i, Smooth (X i).hom)
    (hp : ∀ i, IsProper (X i).hom) (hX : ∀ i, Base.Construction.HasSplitGeometricComponents (X i))
    (src dst : α → ι) (f : ∀ a, X (src a) ⟶ X (dst a)) :
    ∃ (s : Finset K) (M : ι → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
      (p : ∀ i, (X i).left ⟶ (M i).left) (fM : ∀ a, M (src a) ⟶ M (dst a)),
      (∀ i, Smooth (M i).hom ∧ IsProper (M i).hom ∧ Base.Construction.HasSplitGeometricComponents (M i)) ∧
      (∀ i, IsPullback (p i) (X i).hom (M i).hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) ∧
      (∀ a, p (src a) ≫ (fM a).left = (f a).left ≫ p (dst a)) ∧
      (∀ i, GeometricallyConnected (X i).hom → GeometricallyConnected (M i).hom) := by
  obtain ⟨s, M, p, hM, hcart, hconn⟩ := finite_split_models_common_base X hs hp hX
  have hFP (i : ι) : Scheme.Constructions.Foundations.FinitePresentationMorphism (M i).hom := by
    have := (hM i).1
    have := (hM i).2.1
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, h, fM, hfM⟩ := CommonStage.Constructions.Foundations.finite_morphisms_descend src dst X M hFP p hcart f
  refine ⟨t, (fun i ↦ (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj (M i)),
    (fun i ↦ ModelMorphisms.Constructions.Foundations.genericModelLift (M i) (p i) (hcart i).w h), fM, ?_, ?_, hfM, ?_⟩
  · intro i
    have := (hM i).1
    have := (hM i).2.1
    exact ⟨inferInstanceAs (Smooth (pullback.snd (M i).hom _)),
      inferInstanceAs (IsProper (pullback.snd (M i).hom _)),
      SplitComponentsBaseChange.Construction.hasSplitGeometricComponents_baseChange _ (M i) (hM i).2.2⟩
  · intro i
    exact ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian (M i) (p i) (hcart i) h
  · intro i hc
    have := hconn i hc
    exact inferInstanceAs (GeometricallyConnected (pullback.snd (M i).hom _))

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitFinite.Construction
