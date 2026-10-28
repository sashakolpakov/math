import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Reference Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamily

noncomputable section

/-! The full designated ReferenceFamily proposition, expressed without importing
its statement-only declaration. The principal special-unitary condition
is expanded into its defining two equations. -/

def ModuliInput : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ), 0 < s → Module.finrank ℚ E = 2 * s →
    ∀ (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s), P.IsAdmissible →
    ∀ {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ),
    κ.comp iota = P.μ → ∀ (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ),
    0 < M → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N →
        (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
          LinearMap.det g.toLinearMap = 1) ∧
        P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
        ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
          (∀ g, g ∈ Γ ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧ LinearMap.det g.toLinearMap = 1) ∧
          (∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
          ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N,
            S.IsFine ∧ S.HasProjectiveBallComponents κ ∧
            ∃ (C₀ : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
              S.IsProjectiveComponent κ C₀ X ∧ P.IsUniformizedBy X Γ

theorem exists_deep_projective_reference (h43 : ModuliInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 0 < N) :
    ∃ L : ℕ, 3 ≤ L ∧ N ∣ L ∧ ∃ M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota L,
      M.IsFine ∧ M.HasProjectiveBallComponents κ := by
  obtain ⟨L, hL, hNL, hall⟩ := h43 s hs hdegree P hP iota κ hemb ⊤ N hN
  obtain ⟨_, _, Γ, _, _, M, hM, hproj, _⟩ := hall L (by omega) dvd_rfl
  exact ⟨L, hL, hNL, M, hM, hproj⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReferenceFamily
