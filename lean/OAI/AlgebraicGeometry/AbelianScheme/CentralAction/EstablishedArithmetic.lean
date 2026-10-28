import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Arithmetic
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality
import OAI.Algebra.Modules.ElementaryDivisors
import OAI.NumberTheory.ClassGroup.Finiteness

/-! # Established Arithmetic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.EstablishedArithmetic.Construction

/-! Native arithmetic inputs for CentralAction, with no result-level hypotheses. -/

theorem provedFinitenessPrincipalization (E : Type*) [Field E] [NumberField E] :
    Arithmetic.Construction.PrincipalizationInput E :=
  NumberTheory.ClassGroup.Finiteness.fractionalIdeal_pow_principal E

theorem provedElementaryDivisorsInput (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    TateComparison.Duality.ElementaryDivisorsInput R K := by
  intro n π hπ L M hL hM
  let := hL
  let := hM
  exact OAI.Algebra.Modules.ElementaryDivisors.lattices_elementary_divisors π hπ L M

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.EstablishedArithmetic.Construction
