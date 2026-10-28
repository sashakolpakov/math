import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeepLevels

/-! # Arithmetic Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ArithmeticRefinement

noncomputable section

/-! The arithmetic refinement in ReferenceFamily: one level refines a prescribed
modulus, has trivial determinant, lies in the requested adelic open
subgroup, and defines the exact torsion-free principal SU group. -/

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem exists_arithmetic_level_refinement (hP : P.IsAdmissible)
    (H : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ) (hM : 0 < M) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N →
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g → LinearMap.det g.toLinearMap = 1) ∧
      P.adelicPrincipalLevel N ≤ H.toSubgroup ∧
      ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
        (∀ g, g ∈ Γ ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧ LinearMap.det g.toLinearMap = 1) ∧
        ∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1 := by
  obtain ⟨_, _, hb, _, _, _, _, _, _, hΛ, _⟩ := hP
  obtain ⟨D, hD, hcontain⟩ := AdelicContainment.exists_adelic_principal_containment_depth P hΛ.1 hΛ.2.1 H
  obtain ⟨N₀, h3, hMN, hdeep⟩ := DeepLevels.exists_special_torsion_free_refinement
    P.b hb P.lattice hΛ (M * D) (Nat.mul_pos hM hD)
  refine ⟨N₀, h3, (dvd_mul_right M D).trans hMN, ?_⟩
  intro N hN hdiv
  obtain ⟨hdet, hfree⟩ := hdeep N hN hdiv
  have hDN : D ∣ N := (dvd_mul_left D M).trans (hMN.trans hdiv)
  exact ⟨hdet, hcontain N hDN, Groups.principalSpecialUnitary P.b P.lattice N,
    Groups.mem_principalSpecialUnitary P.b P.lattice N, hfree⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ArithmeticRefinement
