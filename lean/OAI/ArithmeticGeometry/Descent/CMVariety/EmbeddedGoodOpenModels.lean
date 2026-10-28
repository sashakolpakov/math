import OAI.ArithmeticGeometry.Descent.CMVariety.GoodOpenCoefficientModels
import OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedCoefficientEnlargement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms

/-! # Embedded Good Open Models -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedGoodOpenModels.Abelian

noncomputable section

/-! Put a constructed geometrically integral open into a smooth proper
embedded coefficient model at a common finite stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms.Coefficients

theorem embedded_model_has_good_open_after_enlargement
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {W X : Over (Spec (.of K))} (f : W ⟶ X)
    [IsOpenImmersion f.left] [CompactSpace W.left]
    (MW : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K W) {n : ℕ} (DX : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n)
    [GeometricallyConnected MW.model.hom] [GeometricallyIrreducible MW.model.hom]
    [Smooth DX.toModel.model.hom] [IsProper DX.toModel.model.hom] :
    ∃ (D : AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveParameters.Coefficients.EmbeddedCoefficientModel R K X n)
      (V : Over (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K D.toModel.coefficients)) (i : V ⟶ D.toModel.model),
      GeometricallyConnected V.hom ∧ GeometricallyIrreducible V.hom ∧
      IsOpenImmersion i.left ∧ Smooth D.toModel.model.hom ∧ IsProper D.toModel.model.hom := by
  classical
  let MX := DX.toModel
  obtain ⟨s₀, ⟨L⟩⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenImmersionStages.Coefficients.open_immersion_has_stage f MX
  let s := s₀ ∪ (MW.coefficients ∪ MX.coefficients)
  have hL : s₀ ⊆ s := Finset.subset_union_left
  have hW : MW.coefficients ⊆ s := Finset.subset_union_left.trans Finset.subset_union_right
  have hX : MX.coefficients ⊆ s := Finset.subset_union_right.trans Finset.subset_union_right
  let L₁ := L.enlarge hL
  let W₁ := MW.enlarge s hW
  let D₁ := EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel DX s hX
  let X₁ := D₁.toModel
  have : GeometricallyConnected W₁.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_connected MW s hW
  have : GeometricallyIrreducible W₁.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_irreducible MW s hW
  have : Smooth X₁.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_smooth MX s hX
  have : IsProper X₁.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_proper MX s hX
  obtain ⟨t, hst, eT, _⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms.Coefficients.isomorphism_between_models_descends
    L₁.target X₁.model L₁.targetFP X₁.finitePresentation L₁.pTarget X₁.specialization
    L₁.targetCartesian X₁.cartesian (Iso.refl X)
  let L₂ := L₁.enlarge hst
  let W₂ := W₁.enlarge t hst
  let D₂ := EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel D₁ t hst
  let X₂ := D₂.toModel
  have : GeometricallyConnected W₂.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_connected W₁ t hst
  have : GeometricallyIrreducible W₂.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_irreducible W₁ t hst
  have : Smooth X₂.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_smooth X₁ t hst
  have : IsProper X₂.model.hom := EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_proper X₁ t hst
  let eT₂ : L₂.target ≅ X₂.model := eT
  obtain ⟨z, htz, eS, _⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms.Coefficients.isomorphism_between_models_descends
    L₂.source W₂.model L₂.sourceFP W₂.finitePresentation L₂.pSource W₂.specialization
    L₂.sourceCartesian W₂.cartesian (Iso.refl W)
  let L₃ := L₂.enlarge htz
  let W₃ := W₂.enlarge z htz
  let D₃ := EmbeddedCoefficientEnlargement.Abelian.enlargeEmbeddedCoefficientModel D₂ z htz
  let eS₃ : L₃.source ≅ W₃.model := eS
  let eT₃ : L₃.target ≅ D₃.toModel.model :=
    (Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)).mapIso eT₂
  have : IsIso eS₃.inv.left := ((Over.forget (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K z)).mapIso eS₃).isIso_inv
  have : IsIso eT₃.hom.left := ((Over.forget (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K z)).mapIso eT₃).isIso_hom
  have : IsOpenImmersion L₃.inclusion.left := L₃.openInclusion
  let i : W₃.model ⟶ D₃.toModel.model := eS₃.inv ≫ L₃.inclusion ≫ eT₃.hom
  exact ⟨D₃, W₃.model, i, EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_connected W₂ z htz,
    EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_irreducible W₂ z htz,
    inferInstanceAs (IsOpenImmersion (eS₃.inv.left ≫ L₃.inclusion.left ≫ eT₃.hom.left)),
    EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_smooth X₂ z htz, EmbeddedCoefficientEnlargement.Abelian.coefficient_enlarge_proper X₂ z htz⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedGoodOpenModels.Abelian
