import Mathlib

/-! # Lattice Levels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LatticeLevels.CM

noncomputable section

/-! Explicit level comparison for two full integral lattices in the same
rational vector space. This permits the independent reference lattice of
CongruenceLevel to be compared with the lattice defining the source ball quotients. -/

open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def rationalSaturation (Λ : Submodule ℤ V) : Submodule ℚ V where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ n • x ∈ Λ}
  zero_mem' := ⟨1, by omega, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have hx' := Λ.smul_mem (m : ℤ) hx
    have hy' := Λ.smul_mem (n : ℤ) hy
    simpa only [smul_add, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm m n x]
      using Λ.add_mem hx' hy'
  smul_mem' := by
    rintro a x ⟨n, hn, hx⟩
    refine ⟨n * a.den, Nat.mul_pos hn a.den_pos, ?_⟩
    have heq : (n * a.den) • (a • x) = a.num • (n • x) := by
      calc
        _ = ((n : ℚ) * ((a.den : ℚ) * a)) • x := by
          rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, Nat.cast_mul, mul_assoc]
        _ = ((a.num : ℚ) * (n : ℚ)) • x := by rw [Rat.den_mul_eq_num, mul_comm]
        _ = a.num • (n • x) := by
          rw [← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    rw [heq]
    exact Λ.smul_mem a.num hx

theorem exists_multiple_mem (Λ : Submodule ℤ V)
    (hfull : Submodule.span ℚ (Λ : Set V) = ⊤) (x : V) :
    ∃ n : ℕ, 0 < n ∧ n • x ∈ Λ := by
  have hs : Submodule.span ℚ (Λ : Set V) ≤ rationalSaturation Λ := by
    apply Submodule.span_le.mpr
    intro y hy
    refine ⟨1, by omega, ?_⟩
    rw [one_smul]
    exact hy
  rw [hfull] at hs
  exact hs (Submodule.mem_top : x ∈ (⊤ : Submodule ℚ V))

/-- A single positive denominator moves one finitely generated lattice
into any other full lattice. -/
theorem exists_uniform_multiple (Λ Γ : Submodule ℤ V)
    (hΛ : Λ.FG) (hΓ : Submodule.span ℚ (Γ : Set V) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ Λ, n • x ∈ Γ := by
  obtain ⟨k, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hΛ
  choose n hn hnf using fun i : Fin k => exists_multiple_mem Γ hΓ (f i)
  let m := ∏ i, n i
  refine ⟨m, Finset.prod_pos (fun i _ => hn i), ?_⟩
  intro x hx
  rw [← hf] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
      have h := Γ.smul_mem (a : ℤ) (hnf i)
      simpa only [m, ha, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm (n i) a (f i)]
        using h
  | zero => simpa only [smul_zero] using Γ.zero_mem
  | add x y _ _ hx hy => simpa only [smul_add] using Γ.add_mem hx hy
  | smul a x _ hx => simpa only [smul_comm m a x] using Γ.smul_mem a hx

def Principal (Λ : Submodule ℤ V) (N : ℕ) (g : V ≃ₗ[ℚ] V) : Prop :=
  (∀ x, x ∈ Λ ↔ g x ∈ Λ) ∧
  ∀ x ∈ Λ, ∃ y ∈ Λ, g x - x = (N : ℤ) • y

theorem principal_inverse {Λ : Submodule ℤ V} {N : ℕ} {g : V ≃ₗ[ℚ] V}
    (h : Principal Λ N g) : Principal Λ N g.symm := by
  refine ⟨fun x => ?_, ?_⟩
  · simpa only [g.apply_symm_apply] using (h.1 (g.symm x)).symm
  · intro x hx
    have hy : g.symm x ∈ Λ := (h.1 (g.symm x)).mpr (by simpa using hx)
    obtain ⟨z, hz, heq⟩ := h.2 (g.symm x) hy
    refine ⟨-z, Λ.neg_mem hz, ?_⟩
    have heq' := congrArg Neg.neg heq
    simpa only [g.apply_symm_apply, neg_sub, smul_neg] using heq'

theorem principal_mono {Λ : Submodule ℤ V} {N M : ℕ} {g : V ≃ₗ[ℚ] V}
    (hdiv : N ∣ M) (h : Principal Λ M g) : Principal Λ N g := by
  obtain ⟨a, rfl⟩ := hdiv
  refine ⟨h.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, heq⟩ := h.2 x hx
  refine ⟨(a : ℤ) • y, Λ.smul_mem _ hy, ?_⟩
  simpa only [Nat.cast_mul, mul_smul] using heq

/-- Clearing the two lattice inclusions gives an explicit sufficient
principal level. The conclusion includes preservation of the new lattice. -/
theorem principal_change_lattice
    (Λ Γ : Submodule ℤ V) (m n N : ℕ) (hm : 0 < m)
    (hΓΛ : ∀ x ∈ Γ, m • x ∈ Λ) (hΛΓ : ∀ x ∈ Λ, n • x ∈ Γ)
    (g : V ≃ₗ[ℚ] V) (hg : Principal Λ (m * (n * N)) g) :
    Principal Γ N g := by
  have hmove : ∀ (f : V ≃ₗ[ℚ] V), Principal Λ (m * (n * N)) f →
      ∀ x ∈ Γ, ∃ y ∈ Γ, f x - x = (N : ℤ) • y := by
    intro f hf x hx
    obtain ⟨y, hy, heq⟩ := hf.2 (m • x) (hΓΛ x hx)
    refine ⟨n • y, hΛΓ y hy, ?_⟩
    have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    apply (smul_right_injective V hmQ)
    have heq' : (m : ℚ) • (f x - x) = (m : ℚ) • ((N : ℤ) • (n • y)) := by
      simpa only [map_nsmul, Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul,
        smul_sub, smul_comm n N y] using heq
    exact heq'
  have hfor := hmove g hg
  have hback := hmove g.symm (principal_inverse hg)
  refine ⟨?_, hfor⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := hfor x hx
    rw [← sub_add_cancel (g x) x, heq]
    exact Γ.add_mem (Γ.smul_mem _ hy) hx
  · intro hx
    obtain ⟨y, hy, heq⟩ := hback (g x) hx
    rw [g.symm_apply_apply] at heq
    rw [← sub_add_cancel x (g x), heq]
    exact Γ.add_mem (Γ.smul_mem _ hy) hx

/-- Any prescribed level for one full lattice contains every sufficiently
divisible principal level for the other lattice. -/
theorem cofinal_principal_levels
    (Λ Γ : Submodule ℤ V) (hΛfg : Λ.FG) (hΓfg : Γ.FG)
    (hΛfull : Submodule.span ℚ (Λ : Set V) = ⊤)
    (hΓfull : Submodule.span ℚ (Γ : Set V) = ⊤)
    (N Nbase : ℕ) (hN : 0 < N) (hNbase : 0 < Nbase) :
    ∃ M : ℕ, 0 < M ∧ Nbase ∣ M ∧
      ∀ L : ℕ, M ∣ L → ∀ g : V ≃ₗ[ℚ] V,
        Principal Λ L g → Principal Γ N g := by
  obtain ⟨m, hm, hΓΛ⟩ := exists_uniform_multiple Γ Λ hΓfg hΛfull
  obtain ⟨n, hn, hΛΓ⟩ := exists_uniform_multiple Λ Γ hΛfg hΓfull
  refine ⟨Nbase * (m * (n * N)), by positivity, dvd_mul_right _ _, ?_⟩
  intro L hL g hg
  apply principal_change_lattice Λ Γ m n N hm hΓΛ hΛΓ g
  exact principal_mono ((dvd_mul_left _ _).trans hL) hg

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LatticeLevels.CM
