import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResolutionDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeQuotientLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.BoundedResolution

/-! # Projective Prime Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ProjectivePrimePrincipal

noncomputable section

/-! A height-one prime whose quotient has finite projective
dimension is principal in a normal Noetherian local domain. The generator comes
from its actual finite free resolution. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [IsIntegrallyClosed R]

theorem principal (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (d : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ p)) d] : p.IsPrincipal := by
  have hp₀ : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hp
    exact zero_ne_one hp
  obtain ⟨r, hrp, hr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp₀
  let M := ModuleCat.of R (R ⧸ p)
  obtain ⟨a, ha, ho⟩ := ResolutionDivisor.exists_equation R M d r hr (PrimeQuotientLocalization.annihilated R p r hrp)
  have he : p = Ideal.span {a} := by
    apply NormalDivisibility.PrimePrincipalFromOrders.span_eq R p hp a ha
    intro q hprime hq
    rw [ho q hq]
    have hlen := PrimeFiltrationMultiplicity.localized_prime_length R
      ⟨q, hprime⟩ ⟨p, inferInstance⟩ hq hp₀
    have heq : (⟨p, inferInstance⟩ : PrimeSpectrum R) = ⟨q, hprime⟩ ↔ q = p := by
      constructor
      · intro h
        exact (congrArg PrimeSpectrum.asIdeal h).symm
      · intro h
        exact PrimeSpectrum.ext h.symm
    change Module.length (Localization.AtPrime q) ((Localization.AtPrime q) ⊗[R] (R ⧸ p)) = _ at hlen
    change Module.length (Localization.AtPrime q) ((Localization.AtPrime q) ⊗[R] (R ⧸ p)) = _
    simpa only [heq] using hlen
  exact ⟨a, he⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ProjectivePrimePrincipal
