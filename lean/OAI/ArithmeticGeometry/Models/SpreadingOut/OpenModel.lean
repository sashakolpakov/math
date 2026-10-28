import OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpen
import OAI.ArithmeticGeometry.Models.Isomorphisms

/-! # Open Model -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.OpenModel.Construction

noncomputable section

/-! Descent of a dense open immersion while retaining geometric properties
of its source model and smooth properness of its target model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

open OAI.ArithmeticGeometry.Models.Isomorphisms.Constructions.Foundations

instance coefficient_enlarge_smooth
    {K : Type u} [Field K] [NumberField K] {X : Over (Spec (.of K))}
    (M : Foundations.Constructions.CoefficientModel K X) [Smooth M.model.hom] (t : Finset K) (h : M.coefficients ⊆ t) :
    Smooth (M.enlarge t h).model.hom :=
  inferInstanceAs (Smooth (pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)))

instance coefficient_enlarge_proper
    {K : Type u} [Field K] [NumberField K] {X : Over (Spec (.of K))}
    (M : Foundations.Constructions.CoefficientModel K X) [IsProper M.model.hom] (t : Finset K) (h : M.coefficients ⊆ t) :
    IsProper (M.enlarge t h).model.hom :=
  inferInstanceAs (IsProper (pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)))

instance coefficient_enlarge_geometricallyConnected
    {K : Type u} [Field K] [NumberField K] {X : Over (Spec (.of K))}
    (M : Foundations.Constructions.CoefficientModel K X) [GeometricallyConnected M.model.hom]
    (t : Finset K) (h : M.coefficients ⊆ t) :
    GeometricallyConnected (M.enlarge t h).model.hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)))

instance coefficient_enlarge_geometricallyIrreducible
    {K : Type u} [Field K] [NumberField K] {X : Over (Spec (.of K))}
    (M : Foundations.Constructions.CoefficientModel K X) [GeometricallyIrreducible M.model.hom]
    (t : Finset K) (h : M.coefficients ⊆ t) :
    GeometricallyIrreducible (M.enlarge t h).model.hom :=
  inferInstanceAs (GeometricallyIrreducible (pullback.snd M.model.hom (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)))

theorem coefficient_enlarge_specialization_eq
    {K : Type u} [Field K] [NumberField K] {X : Over (Spec (.of K))}
    (M : Foundations.Constructions.CoefficientModel K X) (t : Finset K) (h : M.coefficients ⊆ t) :
    (M.enlarge t h).specialization = ModelMorphisms.Constructions.Foundations.genericModelLift M.model M.specialization M.cartesian.w h := by
  simp only [Foundations.Constructions.CoefficientModel.enlarge, Foundations.Constructions.CoefficientModel.ofCartesian_specialization]
  rfl

theorem open_immersion_models_with_geometry
    {K : Type u} [Field K] [NumberField K]
    {W X : Over (Spec (.of K))} (f : W ⟶ X)
    [IsOpenImmersion f.left] [CompactSpace W.left]
    (MW : Foundations.Constructions.CoefficientModel K W) (MX : Foundations.Constructions.CoefficientModel K X)
    [GeometricallyConnected MW.model.hom] [GeometricallyIrreducible MW.model.hom]
    [Smooth MX.model.hom] [IsProper MX.model.hom] :
    ∃ (s : Finset K) (M : OpenImmersionStages.Constructions.Foundations.OpenImmersionAtBase s f),
      GeometricallyConnected M.source.hom ∧ GeometricallyIrreducible M.source.hom ∧
      Smooth M.target.hom ∧ IsProper M.target.hom := by
  classical
  obtain ⟨s₀, ⟨L⟩⟩ := OpenImmersionStages.Constructions.Foundations.open_immersion_has_stage f MX
  let s := s₀ ∪ (MW.coefficients ∪ MX.coefficients)
  have hL : s₀ ⊆ s := Finset.subset_union_left
  have hW : MW.coefficients ⊆ s := Finset.subset_union_left.trans Finset.subset_union_right
  have hX : MX.coefficients ⊆ s := Finset.subset_union_right.trans Finset.subset_union_right
  let L₁ := L.enlarge hL
  let W₁ := MW.enlarge s hW
  let X₁ := MX.enlarge s hX
  have : GeometricallyConnected W₁.model.hom := coefficient_enlarge_geometricallyConnected MW s hW
  have : GeometricallyIrreducible W₁.model.hom := coefficient_enlarge_geometricallyIrreducible MW s hW
  have : Smooth X₁.model.hom := coefficient_enlarge_smooth MX s hX
  have : IsProper X₁.model.hom := coefficient_enlarge_proper MX s hX
  obtain ⟨t, hst, eT, heT⟩ := Isomorphisms.Constructions.Foundations.isomorphism_between_models_descends
    L₁.target X₁.model L₁.targetFP X₁.finitePresentation L₁.pTarget X₁.specialization
    L₁.targetCartesian X₁.cartesian (Iso.refl X)
  let L₂ := L₁.enlarge hst
  let W₂ := W₁.enlarge t hst
  let X₂ := X₁.enlarge t hst
  have : GeometricallyConnected W₂.model.hom := coefficient_enlarge_geometricallyConnected W₁ t hst
  have : GeometricallyIrreducible W₂.model.hom := coefficient_enlarge_geometricallyIrreducible W₁ t hst
  have : Smooth X₂.model.hom := coefficient_enlarge_smooth X₁ t hst
  have : IsProper X₂.model.hom := coefficient_enlarge_proper X₁ t hst
  let eT₂ : L₂.target ≅ X₂.model := eT
  have ht₂ : L₂.pTarget ≫ eT₂.hom.left = X₂.specialization := by
    exact (heT.trans (Category.id_comp _)).trans
      (coefficient_enlarge_specialization_eq X₁ t hst).symm
  obtain ⟨z, htz, eS, heS⟩ := Isomorphisms.Constructions.Foundations.isomorphism_between_models_descends
    L₂.source W₂.model L₂.sourceFP W₂.finitePresentation L₂.pSource W₂.specialization
    L₂.sourceCartesian W₂.cartesian (Iso.refl W)
  let L₃ := L₂.enlarge htz
  let W₃ := W₂.enlarge z htz
  let X₃ := X₂.enlarge z htz
  let eS₃ : L₃.source ≅ W₃.model := eS
  let eT₃ : L₃.target ≅ X₃.model :=
    (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K htz)).mapIso eT₂
  have hs₃ : L₃.pSource ≫ eS₃.hom.left = W₃.specialization := by
    exact (heS.trans (Category.id_comp _)).trans
      (coefficient_enlarge_specialization_eq W₂ z htz).symm
  have ht₃ : L₃.pTarget ≫ eT₃.hom.left = X₃.specialization := by
    have H := BaseChange.Constructions.Foundations.genericModelLift_map L₂.target X₂.model L₂.pTarget X₂.specialization
      L₂.targetCartesian.w X₂.cartesian.w (𝟙 X) eT₂.hom
      (ht₂.trans (Category.id_comp _).symm) htz
    exact (H.trans (Category.id_comp _)).trans
      (coefficient_enlarge_specialization_eq X₂ z htz).symm
  let i : W₃.model ⟶ X₃.model := eS₃.inv ≫ L₃.inclusion ≫ eT₃.hom
  let eSbase := (Over.forget (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K z)).mapIso eS₃
  let eTbase := (Over.forget (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K z)).mapIso eT₃
  have : IsIso eS₃.inv.left := inferInstanceAs (IsIso eSbase.inv)
  have : IsIso eT₃.hom.left := inferInstanceAs (IsIso eTbase.hom)
  have : IsOpenImmersion L₃.inclusion.left := L₃.openInclusion
  have hi : IsOpenImmersion i.left := inferInstanceAs
    (IsOpenImmersion (eS₃.inv.left ≫ L₃.inclusion.left ≫ eT₃.hom.left))
  have hcompat : W₃.specialization ≫ i.left = f.left ≫ X₃.specialization := by
    change W₃.specialization ≫ (eS₃.inv.left ≫ L₃.inclusion.left ≫ eT₃.hom.left) = _
    have hsi : eS₃.hom.left ≫ eS₃.inv.left = 𝟙 _ := eSbase.hom_inv_id
    rw [← hs₃, Category.assoc, ← Category.assoc eS₃.hom.left, hsi,
      Category.id_comp, ← Category.assoc, L₃.compatibility, Category.assoc, ht₃]
  have hWconn : GeometricallyConnected W₃.model.hom :=
    coefficient_enlarge_geometricallyConnected W₂ z htz
  have hWirr : GeometricallyIrreducible W₃.model.hom :=
    coefficient_enlarge_geometricallyIrreducible W₂ z htz
  have hXsmooth : Smooth X₃.model.hom := coefficient_enlarge_smooth X₂ z htz
  have hXproper : IsProper X₃.model.hom := coefficient_enlarge_proper X₂ z htz
  exact ⟨z, {
    source := W₃.model
    target := X₃.model
    sourceFP := W₃.finitePresentation
    targetFP := X₃.finitePresentation
    inclusion := i
    openInclusion := hi
    pSource := W₃.specialization
    pTarget := X₃.specialization
    sourceCartesian := W₃.cartesian
    targetCartesian := X₃.cartesian
    compatibility := hcompat }, hWconn, hWirr, hXsmooth, hXproper⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.OpenModel.Construction
