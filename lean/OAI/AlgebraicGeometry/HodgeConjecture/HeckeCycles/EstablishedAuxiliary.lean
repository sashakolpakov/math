import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum
import OAI.NumberTheory.ArithmeticGroups.CongruenceLevelL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryDivisors
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDuality

/-! # Established Auxiliary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAuxiliary.CM

noncomputable section

/-! Three complete original named inputs supplied by proved native results.
All four ElementaryDivisors clauses and both full CartierDuality conclusions are retained, at arbitrary
universes. The CongruenceLevel reference datum is constructed from its original signature
data. No downstream geometric compatibility is added as a hypothesis. -/

open scoped Classical

universe u

theorem reference_datum (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] (s : ℕ) :
    ReferenceDatum.CM.CongruenceLevelInput E s := by
  intro σ hσ μ b hb hb0 hμ hc dref
  exact NumberTheory.ArithmeticGroups.CongruenceLevelL.reference_polarized_abelian_moduli_datum_unconditional
    σ hσ μ b hb hb0 hμ hc dref

theorem elementary_divisors : AbelianScheme.IsogenyQuotient.ElementaryDivisors.Construction.ElementaryDivisorsInput :=
  AbelianScheme.IsogenyQuotient.ElementaryDivisors.Construction.verified_ElementaryDivisorsInput

theorem cartier_duality_and_blocks : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput :=
  AbelianScheme.FrobeniusKernel.CartierDuality.Construction.fullCartierDualityInput_proved

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAuxiliary.CM
