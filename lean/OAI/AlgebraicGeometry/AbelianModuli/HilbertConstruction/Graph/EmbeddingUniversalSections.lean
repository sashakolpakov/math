import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.UniversalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionsBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentationSectionData

/-! # Embedding Universal Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A complete graph-power embedding over a Noetherian affine tame base
retains complete sections after every affine test. Its chosen bundle need
only be isomorphic to the canonical graph power. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.completeGraphEmbedding_universalSections
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) (D : E.CompleteSectionData) :
    Universal.SectionCompletenessOpen.UniversallyCompleteSectionFamily A.abelian.scheme.hom E.power.sheaf E.sections (𝟙 S) := by
  let C := D.canonicalPowerCompleteData E
  have hs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination A.abelian.scheme.hom.appTop.hom
      (A.graphBundle.tensorPower E.degree).sheaf E.canonicalPowerSectionData.sections) :=
    (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff _ _ _).mpr ⟨C.basis, C.sections_eq.symm⟩
  have h := A.graphPower_completeSections_universal hN hunit E.degree E.degree_pos
    E.canonicalPowerSectionData.sections hs
  let e := (E.isPower.unique (A.graphBundle.tensorPower_isTensorPower E.degree)).some
  exact (Universal.SectionsBundleTransport.universallyCompleteSectionFamily_bundleIso_iff A.abelian.scheme.hom E.sections (𝟙 S) e).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
