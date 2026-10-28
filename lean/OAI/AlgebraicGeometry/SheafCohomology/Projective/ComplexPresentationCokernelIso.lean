import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationAugmentationSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionCokernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolutionFinite

/-! # Complex Presentation Cokernel Iso -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationCokernelIso

noncomputable section

/-! The minimal resolution cokernel is isomorphic to the original coherent sheaf. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField
variable {j : σ} {M : (Proj (homogeneousSubmodule σ ℂ)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M) [M.IsQuasicoherent]

theorem presentationAugmentation_comp_zero :
    ComplexMinimalResolution.ComplexResolution.differential j D.gradedCokernel D.gradedCokernel_nonnegative 0 ≫
      ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D = 0 := by
  have : (ComplexMinimalResolution.ComplexResolution.term j D.gradedCokernel 1).IsQuasicoherent := ComplexMinimalResolutionFinite.ComplexResolution.term_quasicoherent j D.gradedCokernel 1
  have : (ComplexMinimalResolution.ComplexResolution.term j D.gradedCokernel 1).IsFiniteType := ComplexMinimalResolutionFinite.ComplexResolution.term_finiteType j D.gradedCokernel 1
  obtain ⟨b, hb⟩ := ComplexPresentationAugmentationSections.ComplexResolution.presentationAugmentation_eventually_sections D
  apply TwistedSectionsDetectMorphism.MvPolynomial.finiteType_hom_eq_zero_of_eventually_twistedSections_eq_zero _ j b
  intro n hn x
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor
  change G.map (F.map (ComplexMinimalResolution.ComplexResolution.differential j D.gradedCokernel D.gradedCokernel_nonnegative 0 ≫
    ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D)) x = 0
  rw [F.map_comp, G.map_comp, ModuleCat.comp_apply]
  exact (hb n hn).1.apply_apply_eq_zero x

def presentationShortComplex : ShortComplex (Proj (homogeneousSubmodule σ ℂ)).Modules :=
  ShortComplex.mk (ComplexMinimalResolution.ComplexResolution.differential j D.gradedCokernel D.gradedCokernel_nonnegative 0)
    (ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D) (presentationAugmentation_comp_zero D)

theorem presentationShortComplex_exact : (presentationShortComplex D).Exact := by
  have : (ComplexMinimalResolution.ComplexResolution.term j D.gradedCokernel 1).IsQuasicoherent := ComplexMinimalResolutionFinite.ComplexResolution.term_quasicoherent j D.gradedCokernel 1
  have : (ComplexMinimalResolution.ComplexResolution.term j D.gradedCokernel 0).IsQuasicoherent := ComplexMinimalResolutionFinite.ComplexResolution.term_quasicoherent j D.gradedCokernel 0
  have : (ComplexMinimalResolution.ComplexResolution.term j D.gradedCokernel 0).IsFiniteType := ComplexMinimalResolutionFinite.ComplexResolution.term_finiteType j D.gradedCokernel 0
  obtain ⟨b, hb⟩ := ComplexPresentationAugmentationSections.ComplexResolution.presentationAugmentation_eventually_sections D
  exact TwistedSectionsDetectExact.MvPolynomial.finiteType_exact_of_eventually_twistedSections_exact _ _
    (presentationAugmentation_comp_zero D) j b (fun n hn => (hb n hn).1)

theorem presentationAugmentation_epi [M.IsFiniteType] : Epi (ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D) := by
  have : (ComplexMinimalResolution.ComplexResolution.freeSheaf j D.gradedCokernel).IsQuasicoherent := ComplexMinimalResolutionFinite.ComplexResolution.term_quasicoherent j D.gradedCokernel 0
  obtain ⟨b, hb⟩ := ComplexPresentationAugmentationSections.ComplexResolution.presentationAugmentation_eventually_sections D
  exact TwistedSectionsDetectIso.MvPolynomial.finiteType_epi_of_eventually_twistedSections_surjective _ j b (fun n hn => (hb n hn).2)

def presentationCokernelIso [M.IsFiniteType] :
    ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D.gradedCokernel D.gradedCokernel_nonnegative ≅ M := by
  have : Epi (presentationShortComplex D).g := presentationAugmentation_epi D
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (presentationShortComplex_exact D).gIsCokernel

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationCokernelIso
