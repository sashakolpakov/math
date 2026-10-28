import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis

/-! # Section Isomorphism Criteria -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionIsomorphismCriteria

noncomputable section

/-! Actual coefficient section maps retain completeness under bundle
isomorphisms and isomorphisms of the source over the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

private theorem bijective_comp_linearEquiv_iff {R : Type u} [CommRing R]
    {V M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (f : V → M) : Function.Bijective (fun x => e (f x)) ↔ Function.Bijective f := by
  constructor
  · intro h
    refine ⟨fun x y hxy => h.injective (congrArg e hxy), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := h.surjective (e y)
    exact ⟨x, e.injective hx⟩
  · intro h
    exact e.bijective.comp h

theorem coefficientSections_bijective_bundleIso_iff
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    {M N : X.Modules} (e : M ≅ N) {κ : Type v} (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    Function.Bijective (SectionFrameCriterion.coefficientSectionLinearCombination c N (fun i => s i ≫ e.hom)) ↔
      Function.Bijective (SectionFrameCriterion.coefficientSectionLinearCombination c M s) := by
  rw [SectionBundleTransport.coefficientSectionLinearCombination_postcomp]
  exact bijective_comp_linearEquiv_iff (SectionBundleTransport.coefficientBundleSectionEquiv c e)
    (SectionFrameCriterion.coefficientSectionLinearCombination c M s)

theorem coefficientSectionLinearCombination_sourceIso
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) (M : Y.left.Modules)
    {κ : Type v} (s : κ → (Line.Bundles.structureModule Y.left ⟶ M)) :
    SectionFrameCriterion.coefficientSectionLinearCombination X.hom.appTop.hom ((Scheme.Modules.pullback e.hom.left).obj M)
        (fun i => Ample.LineBundles.pullbackSection e.hom.left (s i)) =
      (IsoCoefficientSectionBasis.sourceIsoCoefficientSectionEquiv e M).toLinearMap.comp
        (SectionFrameCriterion.coefficientSectionLinearCombination Y.hom.appTop.hom M s) := by
  have hv : (fun i => RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom _
      (Ample.LineBundles.pullbackSection e.hom.left (s i))) =
    (IsoCoefficientSectionBasis.sourceIsoCoefficientSectionEquiv e M).toLinearMap ∘
      (fun i => RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M (s i)) := by
    funext i
    change _ = RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom _
      (Ample.LineBundles.pullbackSection e.hom.left ((RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M).symm
        (RingSectionBasis.coefficientRingSectionAddEquiv Y.hom.appTop.hom M (s i))))
    rw [AddEquiv.symm_apply_apply]
  change Finsupp.linearCombination Γ(S, ⊤) _ = _
  rw [hv]
  exact Finsupp.linearCombination_linear_comp Γ(S, ⊤) _

theorem coefficientSections_bijective_sourceIso_iff
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) (M : Y.left.Modules)
    {κ : Type v} (s : κ → (Line.Bundles.structureModule Y.left ⟶ M)) :
    Function.Bijective (SectionFrameCriterion.coefficientSectionLinearCombination X.hom.appTop.hom
      ((Scheme.Modules.pullback e.hom.left).obj M) (fun i => Ample.LineBundles.pullbackSection e.hom.left (s i))) ↔
    Function.Bijective (SectionFrameCriterion.coefficientSectionLinearCombination Y.hom.appTop.hom M s) := by
  rw [coefficientSectionLinearCombination_sourceIso]
  exact bijective_comp_linearEquiv_iff (IsoCoefficientSectionBasis.sourceIsoCoefficientSectionEquiv e M)
    (SectionFrameCriterion.coefficientSectionLinearCombination Y.hom.appTop.hom M s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionIsomorphismCriteria
