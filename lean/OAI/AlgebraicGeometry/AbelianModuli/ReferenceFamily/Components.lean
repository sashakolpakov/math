import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConcreteAuxiliaryPureModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentsFromAuxiliaryModel

/-! # Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Components

noncomputable section

/-! The original projective-component and principal special-unitary
conclusion follows from the constructed auxiliary pure model. No
prerequisite proposition is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem moduli_components_unconditional
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K]
    (iota : E →+* K) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (Kaux : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ) (hM : 0 < M) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N →
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
        LinearMap.det g.toLinearMap = 1) ∧
      P.adelicPrincipalLevel N ≤ Kaux.toSubgroup ∧
      ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
        (∀ g, g ∈ Γ ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧ LinearMap.det g.toLinearMap = 1) ∧
        (∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        ∃ S : Models.FinePELModel P iota N,
          S.IsFine ∧ S.HasProjectiveBallComponents κ ∧
          ∃ (C : S.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
            S.IsProjectiveComponent κ C X ∧ P.IsUniformizedBy X Γ := by
  obtain ⟨L, hL, A, ⟨Q⟩, hA⟩ := ConcreteAuxiliaryPureModel.exists_actual_auxiliary_pure_model P hP hs K
  exact ComponentsFromAuxiliaryModel.moduli_components_from_auxiliaryModel s hdegree P hP iota κ hκ A hA hL Q Kaux M hM

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Components
