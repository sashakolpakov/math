import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Definitions

/-! # Moduli -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli.CM

noncomputable section

/-! Apply the complete named ReferenceFamily prerequisite to the reference datum
constructed from the actual source ball. The statement stub is used only
for a compile-time comparison of proposition types, never as a proof. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM

def ModuliConclusion
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    {K : Type} [Field K] [NumberField K]
    (iota : E →+* K) (κ : K →+* ℂ)
    (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ) : Prop :=
  ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧
    ∀ N : ℕ, 0 < N → N₀ ∣ N →
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
        NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
          LinearMap.det g.toLinearMap = 1) ∧
      P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
      ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
        (∀ g, g ∈ Γ ↔ AbelianModuli.ReferenceFamily.Definitions.SpecialUnitaryPrincipalLevel P.b P.lattice N g) ∧
        (∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N,
          S.IsFine ∧ S.HasProjectiveBallComponents κ ∧
          ∃ (C₀ : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
            S.IsProjectiveComponent κ C₀ X ∧ P.IsUniformizedBy X Γ

/-- The full ReferenceFamily proposition, including arbitrary prescribed adelic input
level and arbitrarily deep positive multiples of the resulting level. -/
def ReferenceFamilyInput : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (_hs : 0 < s) (_hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (_hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K]
    (iota : E →+* K) (κ : K →+* ℂ) (_h_embedding : κ.comp iota = P.μ)
    (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ) (_hM : 0 < M),
      ModuliConclusion P iota κ Kaux M

/-- Actual source data now give the full family of deep projective PEL
components. ReferenceFamily is the sole moduli-existence hypothesis at this step. -/
theorem source_moduli_models
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)
    (h_CongruenceLevel : ReferenceDatum.CM.CongruenceLevelInput E places.count) (h_ReferenceFamily : ReferenceFamilyInput)
    (dref : Fin places.count → Bool) :
    ∃ P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count,
      P.IsAdmissible ∧ P.b = B.b ∧ P.embeddings = ReferenceDatum.CM.embeddings E places ∧
        P.distinguished = places.distinguished ∧ P.compactSigns = dref ∧
        ∀ (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ), 0 < M →
          ModuliConclusion P (RingHom.id E) E.val.toRingHom Kaux M := by
  obtain ⟨P, hP, hb, hemb, hdist, hsign⟩ :=
    PELDatum.CM.admissible_reference_datum E B places h_CongruenceLevel dref
  refine ⟨P, hP, hb, hemb, hdist, hsign, ?_⟩
  intro Kaux M hM
  have hμ : E.val.toRingHom.comp (RingHom.id E) = P.μ := by
    rw [RingHom.comp_id]
    unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ
    rw [hemb, hdist, ReferenceDatum.CM.embeddings_distinguished]
  exact h_ReferenceFamily places.count (ReferenceDatum.CM.source_degree E places).1 (ReferenceDatum.CM.source_degree E places).2
    P hP (RingHom.id E) E.val.toRingHom hμ Kaux M hM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli.CM
