import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep

/-! # Residual Source Equiv -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourceEquiv.Constructions

noncomputable section

/-! Residual minimal primes correspond bijectively to the actual
minimal primes of the section ideal in the source quotient. -/

open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourcePrime.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidualMinimalSourcePrime.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveMinimalSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (P : Ideal R) (r : R)

local notation "Q" => R ⧸ P
local notation "A" => R ⧸ Ideal.span (Singleton.singleton r : Set R)
local notation "N" => QuotSMulTop r (R ⧸ P)
local notation "J" => Ideal.span {algebraMap R (R ⧸ P) r}

theorem residualSourcePrime_comap (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    PrimeSpectrum.comap (algebraMap R Q) (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t) =
      PrimeSpectrum.comap (algebraMap R A) t.val :=
  ResidualSourcePrime.Constructions.sourcePrime_comap R P r t.val
    (ResidualMinimalSourcePrime.Constructions.minimal_mem_support R P r t.val ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes A N t.val).mp t.property))

theorem residualSourcePrime_injective : Function.Injective (TorAlgebra.SourceOrderStep.residualSourcePrime R P r) := by
  intro t u h
  apply Subtype.ext
  apply PrimeSpectrum.comap_injective_of_surjective (algebraMap R A) Ideal.Quotient.mk_surjective
  exact (residualSourcePrime_comap R P r t).symm.trans
    ((congrArg (PrimeSpectrum.comap (algebraMap R Q)) h).trans (residualSourcePrime_comap R P r u))

theorem residualSourcePrime_minimal (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t).asIdeal ∈ (J).minimalPrimes :=
  ResidualMinimalSourcePrime.Constructions.sourcePrime_minimal R P r t.val
    (ResidualMinimalSourcePrime.Constructions.minimal_mem_support R P r t.val ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes A N t.val).mp t.property))
    ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes A N t.val).mp t.property)

theorem exists_residualSourcePrime (q : PrimeSpectrum Q) (hq : q.asIdeal ∈ (J).minimalPrimes) :
    ∃ t : TorAlgebra.SourceOrderStep.ResidualComponent R P r, TorAlgebra.SourceOrderStep.residualSourcePrime R P r t = q := by
  have hq' : q.asIdeal ∈ (Module.annihilator Q (Q ⧸ J)).minimalPrimes := by
    rwa [Ideal.annihilator_quotient]
  have hR := (SurjectiveMinimalSupport.Constructions.comap_mem_minimalPrimes_iff R Q (Q ⧸ J) Ideal.Quotient.mk_surjective q).mpr hq'
  have he := (QuotientEquationScalarChange.Constructions.algebraQuotientEquiv R Q r).annihilator_eq
  have hN : (PrimeSpectrum.comap (algebraMap R Q) q).asIdeal ∈ (Module.annihilator R N).minimalPrimes := by
    rw [he]
    exact hR
  obtain ⟨t, ht, hcomap⟩ := SurjectiveMinimalSupport.Constructions.exists_comap_of_minimal R A N Ideal.Quotient.mk_surjective
    (PrimeSpectrum.comap (algebraMap R Q) q) hN
  let u : TorAlgebra.SourceOrderStep.ResidualComponent R P r := ⟨t, (MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes A N t).mpr ht⟩
  refine ⟨u, ?_⟩
  apply PrimeSpectrum.comap_injective_of_surjective (algebraMap R Q) Ideal.Quotient.mk_surjective
  exact (residualSourcePrime_comap R P r u).trans hcomap

def residualSourceEquiv : TorAlgebra.SourceOrderStep.ResidualComponent R P r ≃ {q : PrimeSpectrum Q // q.asIdeal ∈ (J).minimalPrimes} :=
  Equiv.ofBijective (fun t => ⟨TorAlgebra.SourceOrderStep.residualSourcePrime R P r t, residualSourcePrime_minimal R P r t⟩) (by
    constructor
    · intro t u h
      exact residualSourcePrime_injective R P r (congrArg Subtype.val h)
    · intro q
      obtain ⟨t, ht⟩ := exists_residualSourcePrime R P r q.val q.property
      exact ⟨t, Subtype.ext ht⟩)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourceEquiv.Constructions
