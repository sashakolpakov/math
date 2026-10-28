import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Definitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Components

/-! # Component Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentQuotients

noncomputable section

/-! The ReferenceFamily statement, with its proof supplied by the completed development. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Components

variable {E : Type}
  [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [IsGalois ℚ E]

/--
ReferenceFamily: sufficiently divisible full levels give compact projective
PEL moduli components, including the prescribed principal SU quotient.

The moduli property ranges over all test schemes over K and all PEL
families at the prescribed level. Auxiliary markings are not retained
in the final moduli problem.
-/
theorem moduli_components_and_principal_congruence_quotients
    (s : ℕ)
    (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (P : Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K]
    (iota : E →+* K)
    (κ : K →+* ℂ)
    (h_embedding : κ.comp iota = P.μ)
    -- An open subgroup fixing the prescribed finite adelic inputs.
    (Kaux : OpenSubgroup P.FiniteSpecialUnitary)
    (M : ℕ)
    (hM : 0 < M) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N →
        -- Deep unitary level has trivial determinant.
        (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
          NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
            LinearMap.det g.toLinearMap = 1) ∧
        -- The adelic level fixes the finite inputs.
        P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
        ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
          (∀ g,
            g ∈ Γ ↔
              Definitions.SpecialUnitaryPrincipalLevel P.b P.lattice N g) ∧
          (∀ g ∈ Γ, ∀ k : ℕ,
            0 < k → g ^ k = 1 → g = 1) ∧
          ∃ S : Models.FinePELModel P iota N,
            S.IsFine ∧
            S.HasProjectiveBallComponents κ ∧
            ∃ (C₀ : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
              S.IsProjectiveComponent κ C₀ X ∧ P.IsUniformizedBy X Γ := by
  exact Components.moduli_components_unconditional s hs hdegree P hP iota κ h_embedding Kaux M hM

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentQuotients
