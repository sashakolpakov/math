import Mathlib

/-! # Central Constraint -/

namespace OAI.RepresentationTheory.Hecke.CentralConstraint.Construction

/-!
# CentralConstraint: the central constraint, conditional on the supplied inputs

The target already has native algebraic hypotheses. `hprojective` is the
instantiated SphericalAction conclusion, `hcentral` is the H¹ part of CentralAction, `hT₃`
is the central Satake identity from GL3, and `hT₁`, `hT₂` are CosetCalculus.
`he_alg` is the algebraicity input identified in the target formulation.
RationalStructure's rational-descent statement alone does not assert algebraicity of e;
in the manuscript this also uses rational finite-dimensional cohomology.
We retain this original, explicit hypothesis rather than claiming that
rational descent alone proves it. No geometric realization is asserted.

`CommutingInput` is the complete proposition of Commuting, instantiated at the given
commuting family (including triangularization, finiteness and direct sum).
Only its polynomial-identity consequence is needed here. The proof does
not import any statement theorem or use a project placeholder as a fact.

For inverse-coset action the Satake parameters must be inverted along with
the acting convention. `projective_parameter_under_inversion` proves the
required permutation and changes e to e⁻¹; the main theorem then applies
to the correspondingly oriented raw operators and character.
-/

theorem projective_parameter_under_inversion
    {K : Type*} [Field K] (r e : K) (α : Fin 3 → K)
    (hprojective : ∃ a : K, a ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, α i = a * (![r, r⁻¹, e] : Fin 3 → K) (σ i)) :
    ∃ a : K, a ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, (α i)⁻¹ = a * (![r, r⁻¹, e⁻¹] : Fin 3 → K) (σ i) := by
  classical
  obtain ⟨a, ha, σ, hα⟩ := hprojective
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hswap (j : Fin 3) :
      ((![r, r⁻¹, e] : Fin 3 → K) j)⁻¹ =
        (![r, r⁻¹, e⁻¹] : Fin 3 → K) (τ j) := by
    fin_cases j <;> norm_num [τ, Equiv.swap_apply_def]
  refine ⟨a⁻¹, inv_ne_zero ha, σ.trans τ, ?_⟩
  intro i
  rw [hα i, mul_inv_rev, hswap]
  simp [Equiv.trans_apply, mul_comm]

def CommutingInput {K V ι : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : ι → Module.End K V) : Prop :=
  (∀ i j, Commute (T i) (T j)) →
  ∃ ev : MvPolynomial ι K →ₐ[K] Module.End K V,
    (∀ i, ev (MvPolynomial.X i) = T i) ∧
    (∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ i (r c : Fin (Module.finrank K V)),
        c < r → b.repr (T i (b c)) r = 0) ∧
    Set.Finite {χ : ι → K | (⨅ i, (T i).genEigenspace (χ i) ⊤) ≠ ⊥} ∧
    iSupIndep (fun χ : ι → K => ⨅ i, (T i).genEigenspace (χ i) ⊤) ∧
    (⨆ χ : ι → K, ⨅ i, (T i).genEigenspace (χ i) ⊤) = ⊤ ∧
    (∀ (χ : ι → K) (p : MvPolynomial ι K),
      (⨅ i, (T i).genEigenspace (χ i) ⊤) ≠ ⊥ →
      ev p = 0 → MvPolynomial.eval χ p = 0)

theorem eigencharacter_power_of_Commuting
    {K H V : Type*} [Field K] [CommRing H] [Algebra K H]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : H →ₐ[K] Module.End K V) (χ : H →ₐ[K] K)
    (hCommuting : CommutingInput (fun h : H => ρ h))
    (hoccurs : (⨅ h : H, (ρ h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : H) (N : ℕ) (hpow : (ρ h) ^ N = 1) :
    (χ h) ^ N = 1 := by
  have hcomm (i j : H) : Commute (ρ i) (ρ j) := by
    show ρ i * ρ j = ρ j * ρ i
    rw [← map_mul, ← map_mul, mul_comm i j]
  obtain ⟨ev, hev, _, _, _, _, hpoly⟩ := hCommuting hcomm
  have hz := hpoly χ (MvPolynomial.X h ^ N - 1) hoccurs (by
    simp only [map_sub, map_pow, map_one, hev, hpow, sub_self])
  simpa [sub_eq_zero] using hz

theorem symmetric_triple_permutation
    {K : Type*} [Field K] [CharZero K]
    (u : Fin 3 → K) (σ : Equiv.Perm (Fin 3)) :
    (u (σ 0) + u (σ 1) + u (σ 2) = u 0 + u 1 + u 2) ∧
    (u (σ 0) * u (σ 1) + u (σ 0) * u (σ 2) + u (σ 1) * u (σ 2) =
      u 0 * u 1 + u 0 * u 2 + u 1 * u 2) ∧
    (u (σ 0) * u (σ 1) * u (σ 2) = u 0 * u 1 * u 2) := by
  have hsum := Equiv.sum_comp σ u
  have hprod := Equiv.prod_comp σ u
  have hsquares := Equiv.sum_comp σ (fun i => u i ^ 2)
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_zero,
    Fin.prod_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    add_zero, mul_one] at hsum hprod hsquares
  refine ⟨by simpa [add_assoc] using hsum, ?_, by simpa [mul_assoc] using hprod⟩
  apply mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0)
  linear_combination
    (u (σ 0) + u (σ 1) + u (σ 2) + (u 0 + u 1 + u 2)) * hsum - hsquares

/-- Central constraint for any occurring full Satake extension. -/
theorem central_constraint_on_full_satake_extensions
    {K H V : Type*}
    [Field K] [CharZero K] [Algebra ℚ K] [IsAlgClosed K]
    [CommRing H] [Algebra K H]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : H →ₐ[K] Module.End K V)
    (χ : H →ₐ[K] K)
    (hCommuting : CommutingInput (fun h : H => ρ h))
    (q : ℕ) (hq : q.Prime)
    (r e : K)
    (hr : r ^ 2 = (q : K))
    (he : e ≠ 0)
    (he_alg : IsAlgebraic ℚ e)
    (T₁ T₂ T₃ C₀ : H)
    (α : Fin 3 → K)

    -- χ occurs in a nonzero simultaneous generalized eigenspace
    -- of the full H¹ action.
    (hoccurs :
      (⨅ h : H, (ρ h).genEigenspace (χ h) ⊤) ≠ ⊥)

    -- CentralAction: finite order on the entire cohomology space.
    (hcentral :
      ∃ N : ℕ, 0 < N ∧
        (ρ T₃) ^ N = 1 ∧ (ρ C₀) ^ N = 1)

    -- α is the active triple before absorbing χ(C₀).
    -- These are the normalized Satake identities.
    (hT₁ :
      χ T₁ = (q : K) * (α 0 + α 1 + α 2))
    (hT₂ :
      χ T₂ = (q : K) *
        (α 0 * α 1 + α 0 * α 2 + α 1 * α 2))
    (hT₃ :
      χ T₃ = α 0 * α 1 * α 2)

    -- The projective parameter supplied by SphericalAction,
    -- retaining multiplicities and allowing permutation.
    (hprojective :
      ∃ a : K, a ≠ 0 ∧
        ∃ σ : Equiv.Perm (Fin 3),
          ∀ i, α i = a * (![r, r⁻¹, e] : Fin 3 → K) (σ i)) :

    ∃ b : K, ∃ σ : Equiv.Perm (Fin 3),
      b ≠ 0 ∧
      IsAlgebraic ℚ b ∧
      (∀ i, IsAlgebraic ℚ (α i)) ∧

      -- Absorption of the C₀ eigenvalue.
      (∀ i,
        χ C₀ * α i =
          b * (![r, r⁻¹, e] : Fin 3 → K) (σ i)) ∧

      -- The determinant is controlled by the two central actions.
      b ^ 3 * e = (χ C₀) ^ 3 * χ T₃ ∧
      (∃ n : ℕ, 0 < n ∧
        (b ^ 3 * e) ^ n = 1 ∧
        ∀ γ : K ≃ₐ[ℚ] K,
          ((γ b) ^ 3 * γ e) ^ n = 1) ∧

      -- Minuscule eigenvalues after absorption.
      χ (C₀ * T₁) =
        (q : K) * b * (r + r⁻¹ + e) ∧
      χ (C₀ ^ 2 * T₂) =
        (q : K) * b ^ 2 *
          (r * r⁻¹ + r * e + r⁻¹ * e) := by
  classical
  obtain ⟨N, hN, hTN, hCN⟩ := hcentral
  have hTNχ := eigencharacter_power_of_Commuting ρ χ hCommuting hoccurs T₃ N hTN
  have hCNχ := eigencharacter_power_of_Commuting ρ χ hCommuting hoccurs C₀ N hCN
  have hCne : χ C₀ ≠ 0 := by
    intro hzero
    simp [hzero, ne_of_gt hN] at hCNχ
  have hTalg : IsAlgebraic ℚ (χ T₃) :=
    IsAlgebraic.of_pow hN (by rw [hTNχ]; exact isAlgebraic_one)
  have hCalg : IsAlgebraic ℚ (χ C₀) :=
    IsAlgebraic.of_pow hN (by rw [hCNχ]; exact isAlgebraic_one)
  have hrne : r ≠ 0 := by
    intro hzero
    have hz : (q : K) = 0 := by simpa [hzero] using hr.symm
    exact hq.ne_zero (Nat.cast_eq_zero.mp hz)
  have hralg : IsAlgebraic ℚ r :=
    IsAlgebraic.of_pow (by decide : 0 < 2)
      (by rw [hr]; exact isAlgebraic_natCast q)
  obtain ⟨a, hane, σ, hα⟩ := hprojective
  let u : Fin 3 → K := ![r, r⁻¹, e]
  have hu_alg (i : Fin 3) : IsAlgebraic ℚ (u i) := by
    fin_cases i
    · exact hralg
    · exact hralg.inv
    · exact he_alg
  obtain ⟨hsum, hpair, hprod⟩ := symmetric_triple_permutation u σ
  have hαsum : α 0 + α 1 + α 2 = a * (r + r⁻¹ + e) := by
    calc
      _ = a * (u (σ 0) + u (σ 1) + u (σ 2)) := by
        simp only [hα]; dsimp [u]; ring
      _ = _ := by rw [hsum]; rfl
  have hαpair : α 0 * α 1 + α 0 * α 2 + α 1 * α 2 =
      a ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e) := by
    calc
      _ = a ^ 2 * (u (σ 0) * u (σ 1) + u (σ 0) * u (σ 2) +
          u (σ 1) * u (σ 2)) := by
        simp only [hα]; dsimp [u]; ring
      _ = _ := by rw [hpair]; rfl
  have hαprod : α 0 * α 1 * α 2 = a ^ 3 * e := by
    calc
      _ = a ^ 3 * (u (σ 0) * u (σ 1) * u (σ 2)) := by
        simp only [hα]; dsimp [u]; ring
      _ = _ := by rw [hprod]; simp [u, hrne]
  have hdet : χ T₃ = a ^ 3 * e := hT₃.trans hαprod
  have ha_alg : IsAlgebraic ℚ a := by
    apply IsAlgebraic.of_pow (by decide : 0 < 3)
    have hz := hTalg.mul he_alg.inv
    simp only [← div_eq_mul_inv] at hz
    simpa [hdet, he] using hz
  let b : K := χ C₀ * a
  have hbdet : b ^ 3 * e = (χ C₀) ^ 3 * χ T₃ := by
    rw [hdet]; dsimp [b]; ring
  have hbN : (b ^ 3 * e) ^ N = 1 := by
    rw [hbdet, mul_pow, ← pow_mul, Nat.mul_comm 3 N, pow_mul, hCNχ, hTNχ]
    simp
  refine ⟨b, σ, mul_ne_zero hCne hane, hCalg.mul ha_alg, ?_, ?_, hbdet,
    ⟨N, hN, hbN, ?_⟩, ?_, ?_⟩
  · intro i
    rw [hα i]
    exact ha_alg.mul (hu_alg (σ i))
  · intro i
    rw [hα i]
    dsimp [b]
    ring
  · intro γ
    have hz := congrArg γ hbN
    simpa only [map_pow, map_mul, map_one] using hz
  · rw [map_mul, hT₁, hαsum]
    dsimp [b]
    ring
  · rw [map_mul, map_pow, hT₂, hαpair]
    dsimp [b]
    ring

end OAI.RepresentationTheory.Hecke.CentralConstraint.Construction
