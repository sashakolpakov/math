import OAI.AlgebraicGeometry.ComplexMultiplication.CMCore
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.Polarization

/-! # CM Known Results -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM

noncomputable section

/-!
# Explicit interfaces for established background theorems

These are proposition definitions, not axioms or proofs of the propositions.
The conditional development accepts them as named theorem parameters.
See `KNOWN_RESULTS.md` for sources and the scope of each interface.
No CM Hodge conjecture, four-factor switch cycle, theta nonvanishing, or
Hecke--Frobenius congruence is included as a background assumption here.
-/

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

/-- A realization in an actual abelian variety's rational singular `H¹`,
with both Hodge types compared through the canonical coefficient map. -/
structure HodgeRealization (H : WeightOne.CM.WeightOneHodgeStructure U) where
  abelianVariety : CMAbelianVariety.CM.AbelianVariety
  comparison : U ≃ₗ[ℚ] abelianVariety.variety.rationalCohomology 1
  holomorphic : ∀ x, comparison.toLinearMap.baseChange ℂ x ∈ abelianVariety.h1Holomorphic ↔
    x ∈ H.holomorphic
  antiholomorphic : ∀ x, comparison.toLinearMap.baseChange ℂ x ∈ abelianVariety.h1Antiholomorphic ↔
    x ∈ H.antiholomorphic

namespace KnownResults

/-- Riemann realization, in rational cohomological weight-one form.
Source: Milne, *Shimura varieties and moduli*, Theorems 4.4 and 7.12,
after choosing a lattice, clearing denominators, and dualizing homology. -/
def RiemannH1Realization (U : Type*) [AddCommGroup U] [Module ℚ U] : Prop :=
  ∀ H : WeightOne.CM.WeightOneHodgeStructure U, Nonempty (CM.Polarization.WeightOnePolarization H) →
    Nonempty (HodgeRealization H)

/-- Fundamental classes of complex algebraic subvarieties have Hodge type
equal to their codimension. Source: Deligne, *The Hodge Conjecture*, §1. -/
def CycleClassesAreHodge : Prop :=
  ∀ (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ),
    V.geometricAlgebraicClasses p ≤ V.rationalHodgeClasses p

/-- The rational Lefschetz `(1,1)` theorem for the project's actual cycle map.
Source: Deligne, *The Hodge Conjecture*, §2 (divisor classes). -/
def LefschetzOneOne : Prop :=
  ∀ V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety,
    V.rationalHodgeClasses 1 ≤ V.geometricAlgebraicClasses 1

theorem codimension_one (hcycle : CycleClassesAreHodge) (hlefschetz : LefschetzOneOne)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.geometricAlgebraicClasses 1 = V.rationalHodgeClasses 1 :=
  le_antisymm (hcycle V 1) (hlefschetz V)

end KnownResults

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM
