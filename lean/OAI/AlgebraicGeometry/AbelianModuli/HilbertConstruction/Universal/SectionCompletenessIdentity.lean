import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionIsomorphismCriteria
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Section Completeness Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessIdentity

noncomputable section

/-! Universal completeness at the identity of an affine base gives the
actual coefficient basis on the original family through the canonical
identity-pullback comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem universallyCompleteSectionFamily_id_bijective
    {S : Scheme.{u}} [IsAffine S] (X : Over S) (M : X.left.Modules)
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X.left ⟶ M))
    (h : SectionCompletenessOpen.UniversallyCompleteSectionFamily X.hom M s (𝟙 S)) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination X.hom.appTop.hom M s) := by
  have he := Coefficient.SectionIsomorphismCriteria.coefficientSections_bijective_sourceIso_iff (Over.pullbackId.app X) M s
  change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom (𝟙 S)).appTop.hom
      ((Scheme.Modules.pullback (Over.pullbackId.hom.app X).left).obj M)
      (fun i => Ample.LineBundles.pullbackSection (Over.pullbackId.hom.app X).left (s i))) ↔ _ at he
  rw [Moduli.Coherence.pullbackId_hom_left] at he
  apply he.mp
  have hh := h S (𝟙 S)
  change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom (𝟙 S ≫ 𝟙 S)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom (𝟙 S ≫ 𝟙 S))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom (𝟙 S ≫ 𝟙 S)) (s i))) at hh
  rw [Category.id_comp] at hh
  exact hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessIdentity
