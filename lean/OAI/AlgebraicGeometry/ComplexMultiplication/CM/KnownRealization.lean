import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults
import OAI.AlgebraicGeometry.ComplexMultiplication.Comparison
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Known Realization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Geometric realization using Riemann's established theorem

The rational CM polarizations have already been proved in Lean. Applying
the explicit Riemann-realization hypothesis gives abelian varieties with
the prescribed actual `H¹`. This supplies the realization needed by the
conditional route without further work on a projective theta embedding.
-/

open scoped TensorProduct

section

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (R : CMKnownResults.CM.HodgeRealization H)

/-- The complex comparison ends in ordinary singular cohomology, using its
canonical coefficient-extension isomorphism. -/
def CMKnownResults.CM.HodgeRealization.complexComparison : WeightOne.CM.Complexification U ≃ₗ[ℂ]
    R.abelianVariety.variety.complexCohomology 1 := by
  let : Module.Finite ℚ U := H.finiteDimensional
  let : Module.Finite ℚ (R.abelianVariety.variety.rationalCohomology 1) :=
    Module.Finite.of_surjective R.comparison.toLinearMap R.comparison.surjective
  exact (R.comparison.baseChange ℚ ℂ _ _).trans
    (CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace R.abelianVariety.toOver) 1)

theorem CMKnownResults.CM.HodgeRealization.complexComparison_apply (x : WeightOne.CM.Complexification U) :
    R.complexComparison x = R.abelianVariety.h1ScalarExtension
      (R.comparison.toLinearMap.baseChange ℂ x) := rfl

theorem CMKnownResults.CM.HodgeRealization.complexComparison_holomorphic (x : WeightOne.CM.Complexification U) :
    R.complexComparison x ∈ R.abelianVariety.variety.pureBettiSubspace 1 0 ↔
      x ∈ H.holomorphic := R.holomorphic x

theorem CMKnownResults.CM.HodgeRealization.complexComparison_antiholomorphic (x : WeightOne.CM.Complexification U) :
    R.complexComparison x ∈ R.abelianVariety.variety.pureBettiSubspace 0 1 ↔
      x ∈ H.antiholomorphic := R.antiholomorphic x

end

namespace CM

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

/-- Every prescribed CM type is realized geometrically under Riemann's theorem;
its required polarization is the one already constructed and proved. -/
theorem TypeHodgeStructure.CMEmbeddingType.exists_hodgeRealization (hR : CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (ε : TypeHodgeStructure.CMEmbeddingType E) : Nonempty (CMKnownResults.CM.HodgeRealization ε.hodgeStructure) :=
  hR ε.hodgeStructure ⟨ε.polarization⟩

end CM

namespace CM.KnownRealization.CMCoefficientField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

/-- The intermediate odd types in the existing sign-switch chain admit
actual abelian realizations under the same established background theorem. -/
theorem exists_hodgeRealization (hR : CMKnownResults.CM.KnownResults.RiemannH1Realization K)
    (v : OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    Nonempty (CMKnownResults.CM.HodgeRealization (GaloisCMType.CM.CMCoefficientField.hodgeStructure K v)) :=
  hR (GaloisCMType.CM.CMCoefficientField.hodgeStructure K v) ⟨GaloisCMType.CM.CMCoefficientField.hodgeStructure_polarization K v⟩

end CM.KnownRealization.CMCoefficientField

end

end OAI.AlgebraicGeometry.ComplexMultiplication
