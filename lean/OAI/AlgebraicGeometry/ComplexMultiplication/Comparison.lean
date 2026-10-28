import OAI.AlgebraicGeometry.ComplexMultiplication.CMCore
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Full degree-one coefficient comparison under the CM hypothesis

The canonical map from complexified rational `H¹` onto ordinary complex
`H¹` is an isomorphism. The finiteness required for surjectivity comes from
the manuscript's weight-one Hodge-structure hypothesis. Its prescribed
pure subspaces are consequently the full holomorphic and antiholomorphic
subspaces in complex cohomology.
-/

/-- The finite-dimensionality in a CM Hodge decomposition implies
surjectivity of the actual coefficient-extension map in degree one. -/
theorem CMAbelianVariety.CM.AbelianVariety.HasCMH1.h1ScalarExtension_surjective {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    Function.Surjective A.h1ScalarExtension := by
  obtain ⟨H, _, _, _⟩ := h
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) := H.finiteDimensional
  exact CohomologyBaseChange.CM.singularCohomologyComplexification_surjective (Betti.Scheme.schemePointSpace A.toOver) 1

/-- The CM hypothesis uses all ordinary complex `H¹`. -/
theorem CMAbelianVariety.CM.AbelianVariety.HasCMH1.h1ScalarExtension_bijective {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    Function.Bijective A.h1ScalarExtension := by
  obtain ⟨H, _, _, _⟩ := h
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) := H.finiteDimensional
  exact (CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace A.toOver) 1).bijective

/-- The canonical comparison as a complex linear equivalence, proved from
the actual coefficient map. -/
def CMAbelianVariety.CM.AbelianVariety.HasCMH1.h1ScalarExtensionEquiv {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    WeightOne.CM.Complexification (A.variety.rationalCohomology 1) ≃ₗ[ℂ]
      A.variety.complexCohomology 1 :=
  LinearEquiv.ofBijective A.h1ScalarExtension h.h1ScalarExtension_bijective

/-- The holomorphic subspace of complexified rational `H¹` maps onto the
full holomorphic pure-form subspace in ordinary complex cohomology. -/
theorem CMAbelianVariety.CM.AbelianVariety.HasCMH1.map_h1Holomorphic {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    A.h1Holomorphic.map A.h1ScalarExtension = A.variety.pureBettiSubspace 1 0 :=
  Submodule.map_comap_eq_of_surjective h.h1ScalarExtension_surjective _

/-- The same assertion holds for the antiholomorphic subspace. -/
theorem CMAbelianVariety.CM.AbelianVariety.HasCMH1.map_h1Antiholomorphic {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    A.h1Antiholomorphic.map A.h1ScalarExtension = A.variety.pureBettiSubspace 0 1 :=
  Submodule.map_comap_eq_of_surjective h.h1ScalarExtension_surjective _

/-- The actual degree-one pure Betti subspaces form a direct-sum decomposition
when the manuscript's CM hypothesis is satisfied. -/
theorem CMAbelianVariety.CM.AbelianVariety.HasCMH1.pureBetti_isCompl {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    IsCompl (A.variety.pureBettiSubspace 1 0) (A.variety.pureBettiSubspace 0 1) := by
  have hb := h.h1ScalarExtension_bijective
  have hm := h.map_h1Holomorphic
  have ham := h.map_h1Antiholomorphic
  obtain ⟨H, hh, ha, _⟩ := h
  have hcomp := H.complementary
  rw [hh, ha] at hcomp
  have ht := (Submodule.orderIsoMapComapOfBijective A.h1ScalarExtension
    hb).isCompl_iff.mp hcomp
  change IsCompl (A.h1Holomorphic.map A.h1ScalarExtension)
    (A.h1Antiholomorphic.map A.h1ScalarExtension) at ht
  rwa [hm, ham] at ht

end

end OAI.AlgebraicGeometry.ComplexMultiplication
