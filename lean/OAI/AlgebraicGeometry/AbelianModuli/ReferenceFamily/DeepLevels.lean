import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LevelMatrices
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence
import OAI.NumberTheory.ArithmeticGroups.TorsionFreeLevel

/-! # Deep Levels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeepLevels

noncomputable section

/-! Construct sufficiently divisible lattice levels with trivial
unitary determinant and no nonidentity torsion. The depth comes from
actual lattice denominators, independently of any moduli construction. -/

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- Deep principal unitary levels lie in the special unitary group.
The depth is constructed by clearing lattice denominators at modulus 3. -/
theorem exists_determinant_one_depth (b : E) (hb : b ≠ 0)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      ∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ N g → LinearMap.det g.toLinearMap = 1 := by
  obtain ⟨D, hD, hdepth⟩ := Integral.LevelMatrices.exists_integral_matrix_congruence_depth Λ hΛ.1 hΛ.2.1 3 (by omega)
  refine ⟨D, hD, ?_⟩
  intro N hN g hg
  obtain ⟨a, ha, he⟩ := DeterminantCongruence.integral_matrix_determinant_congruence
    (LinearMap.toMatrix' g.toLinearMap) 3 (hdepth N hN g hg.2.2)
  rw [LinearMap.det_toMatrix'] at he
  exact DeterminantCongruence.norm_one_integral_congruence_eq_one (LinearMap.det g.toLinearMap) a ha 3
    (by omega) he (UnitaryDeterminant.unitary_det_norm_one b hb g hg.1)

/-- Determinant triviality and torsion-freeness hold simultaneously
on all positive multiples of a level refining any prescribed modulus. -/
theorem exists_special_torsion_free_refinement (b : E) (hb : b ≠ 0)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (M : ℕ) (hM : 0 < M) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N →
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ N g → LinearMap.det g.toLinearMap = 1) ∧
      (∀ g ∈ Groups.principalSpecialUnitary b Λ N, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) := by
  obtain ⟨D, hD, hdet⟩ := exists_determinant_one_depth b hb Λ hΛ
  have hprod : 0 < D * M := Nat.mul_pos hD hM
  have h3 : 3 ≤ 3 * (D * M) := by omega
  refine ⟨3 * (D * M), h3, dvd_mul_of_dvd_right (dvd_mul_left M D) 3, ?_⟩
  intro N hN hdiv
  have hDN : D ∣ N := (dvd_mul_of_dvd_right (dvd_mul_right D M) 3).trans hdiv
  refine ⟨hdet N hDN, ?_⟩
  intro g hg k hk hpow
  exact NumberTheory.ArithmeticGroups.Levels.CongruenceLevel.principalLevel_torsion_free b Λ hΛ N (h3.trans (Nat.le_of_dvd hN hdiv)) g
    ((Groups.mem_principalSpecialUnitary b Λ N g).mp hg).1 k hk hpow

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeepLevels
