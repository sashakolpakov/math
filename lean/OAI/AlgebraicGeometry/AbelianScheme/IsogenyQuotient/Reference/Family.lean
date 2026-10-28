import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.Family.Construction

noncomputable section

/-!
The complete repaired ReferenceFamily proposition is a named conditional input.
The determinant, auxiliary adelic level, torsion-freeness, projective
components, and native uniformization clauses are all retained. Its
statement-only theorem is not imported or invoked as a proof.
-/

def ReferenceFamilyInput : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (_hs : 0 < s) (_hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (_hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (_h_embedding : κ.comp iota = P.μ) (Kaux : OpenSubgroup P.FiniteSpecialUnitary)
    (M : ℕ) (_hM : 0 < M),
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N →
        (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
          NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g → LinearMap.det g.toLinearMap = 1) ∧
        P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
        ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
          (∀ g, g ∈ Γ ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧ LinearMap.det g.toLinearMap = 1) ∧
          (∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
          ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N,
            S.IsFine ∧ S.HasProjectiveBallComponents κ ∧
            ∃ (C₀ : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
              S.IsProjectiveComponent κ C₀ X ∧ P.IsUniformizedBy X Γ

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.Family.Construction
