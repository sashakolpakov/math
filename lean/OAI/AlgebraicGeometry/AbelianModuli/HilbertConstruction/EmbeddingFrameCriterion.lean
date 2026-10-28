import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion

/-! # Embedding Frame Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The complete-section condition for a power embedding is the
bijectivity of its specified coefficient map, with no choice of a new
section family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.sectionCoefficientMap :
    (Fin (E.dimension + 1) →₀ Γ(S, ⊤)) →ₗ[Γ(S, ⊤)]
      (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor X.hom.appTop.hom).obj E.power.sheaf :=
  Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination X.hom.appTop.hom E.power.sheaf E.sections

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.hasCompleteSections_iff_bijective :
    E.HasCompleteSections ↔ Function.Bijective E.sectionCoefficientMap := by
  change E.HasCompleteSections ↔ Function.Bijective
    (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination X.hom.appTop.hom E.power.sheaf E.sections)
  rw [Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff]
  constructor
  · rintro ⟨D⟩
    exact ⟨D.basis, D.sections_eq.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨⟨b, hb.symm⟩⟩

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.coefficientEquiv (D : E.CompleteSectionData) :
    (Fin (E.dimension + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)]
      (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor X.hom.appTop.hom).obj E.power.sheaf :=
  LinearEquiv.ofBijective E.sectionCoefficientMap (E.hasCompleteSections_iff_bijective.mp ⟨D⟩)

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.coefficientEquiv_single (D : E.CompleteSectionData)
    (i : Fin (E.dimension + 1)) :
    D.coefficientEquiv E (Finsupp.single i 1) =
      Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv X.hom.appTop.hom E.power.sheaf (E.sections i) :=
  Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single X.hom.appTop.hom E.power.sheaf E.sections i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
