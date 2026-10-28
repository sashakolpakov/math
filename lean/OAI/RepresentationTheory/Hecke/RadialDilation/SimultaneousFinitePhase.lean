import Mathlib

/-! # Simultaneous Finite Phase -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SimultaneousFinitePhase.Realization

noncomputable section

/-! A finite family of local finite-phase stabilizations admits one common positive power. -/

open scoped Classical

theorem linearAction_pow_eigen {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : G →* (V ≃ₗ[ℂ] V)) (g : G) (f : V) (ξ : ℂ) (hf : ρ g f = ξ • f) (k : ℕ) :
    ρ (g ^ k) f = ξ ^ k • f := by
  induction k with
  | zero => simp
  | succ k hk =>
      rw [pow_succ, map_mul]
      change ρ (g ^ k) (ρ g f) = _
      rw [hf, map_smul, hk, smul_smul, ← pow_succ']

theorem common_positive_power_finite_phase
    {I : Type*} [Fintype I] {G V : I → Type*}
    [∀ i, Group (G i)] [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, G i →* (V i ≃ₗ[ℂ] V i)) (g : ∀ i, G i) (f : ∀ i, V i)
    (hlocal : ∀ i, ∃ (m : ℕ) (ξ : ℂ), 0 < m ∧ ξ ^ 8 = 1 ∧ ρ i (g i ^ m) (f i) = ξ • f i) :
    ∃ (N : ℕ) (ξ : I → ℂ), 0 < N ∧ ∀ i, ξ i ^ 8 = 1 ∧ ρ i (g i ^ N) (f i) = ξ i • f i := by
  choose m z hm hz hf using hlocal
  let N := ∏ i, m i
  have hN : 0 < N := Finset.prod_pos (fun i _ => hm i)
  refine ⟨N, fun i => z i ^ (N / m i), hN, ?_⟩
  intro i
  have hdiv : m i ∣ N := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hmul : m i * (N / m i) = N := Nat.mul_div_cancel' hdiv
  constructor
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  · change ρ i (g i ^ N) (f i) = z i ^ (N / m i) • f i
    have hpow : g i ^ N = (g i ^ m i) ^ (N / m i) := by rw [← pow_mul, hmul]
    rw [hpow]
    exact linearAction_pow_eigen (ρ i) (g i ^ m i) (f i) (z i) (hf i) (N / m i)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SimultaneousFinitePhase.Realization
