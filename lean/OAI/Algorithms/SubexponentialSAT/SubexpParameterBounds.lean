import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSchedule
import OAI.Algorithms.SubexponentialSAT.SubexpParameters
import OAI.Algorithms.SubexponentialSAT.SubexpRuntime

namespace OAI.Algorithms

/-!
# Polynomial bounds for every actual growing parameter

The record below uses the computed schedule, with an arbitrary actual leaf
factor count satisfying m ≤ ΔD. Its entries include p^k explicitly.
For fixed k the polynomial coefficient and degree are chosen before n and m.
No hypothesis declaring the whole record polynomially bounded is assumed.
-/

namespace SubexponentialSAT.SubexpParameterBounds

open Filter
open SubexponentialSAT.SubexpPackingParameters

/-- All arguments of the counting/construction polynomial, at the actual
computed schedule and the actual leaf's factor count. -/
def parameters (k : ℕ) (hk : 2 ≤ k) (n m : ℕ) :
    SubexponentialSAT.SubexpRuntime.GrowingParameters where
  D := D n
  Q := SubexponentialSAT.SubexpSchedule.Q n
  R := SubexponentialSAT.SubexpSchedule.R k hk n
  h := 4
  m := m
  r := r n
  p := p n
  k := k
  incidence := SubexponentialSAT.SubexpSchedule.delta k hk n
  blockSize := SubexponentialSAT.SubexpSchedule.N k hk n

theorem D_le_n {n : ℕ} (hn : GoodInput n) : D n ≤ n := by
  apply (D_le_iff hn).mpr
  exact Nat.le_mul_of_pos_right n (ell_pos hn)

/-- A loose input-polynomial bound for the actually selected prime. -/
theorem p_le_n {n : ℕ} (hn : GoodInput n) : p n ≤ n := by
  have hu : u n + 1 ≤ s n := by
    have hs := sixteen_mul_u_le n
    have hpos := u_ge_two hn
    omega
  calc
    p n ≤ 2 ^ (u n + 1) := (p_upper hn).le
    _ ≤ 2 ^ s n := Nat.pow_le_pow_right (by decide) hu
    _ ≤ Nat.log2 n := pow_s_le_log2 (goodInput_two_le hn)
    _ ≤ n := Nat.log2_le_self n

theorem Q_le_p_pow_four (n : ℕ) : SubexponentialSAT.SubexpSchedule.Q n ≤ p n ^ 4 :=
  Nat.sub_le _ _

theorem R_le_Q (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    SubexponentialSAT.SubexpSchedule.R k hk n ≤ SubexponentialSAT.SubexpSchedule.Q n :=
  Nat.div_le_self _ _

/-- A finite simultaneous bound, after only the incidence and block-size
bounds have been supplied. Those two bounds are discharged below from the
actual schedule and the proved subpolynomial block-size theorem. -/
theorem entries_le_of_incidence_block_bounds
    (k : ℕ) (hk : 2 ≤ k) (C d n m : ℕ)
    (hn : GoodInput n)
    (hdelta : SubexponentialSAT.SubexpSchedule.delta k hk n ≤ C * (n + 1) ^ d)
    (hblock : SubexponentialSAT.SubexpSchedule.N k hk n ≤ n)
    (hm : m ≤ SubexponentialSAT.SubexpSchedule.delta k hk n * D n) :
    ∀ x ∈ (parameters k hk n m).entries,
      x ≤ (C + k + 5) * (n + 1) ^ (d + k + 5) := by
  let A := C + k + 5
  let e := d + k + 5
  let B := A * (n + 1) ^ e
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hp : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hpow (a : ℕ) (ha : a ≤ e) : (n + 1) ^ a ≤ (n + 1) ^ e :=
    Nat.pow_le_pow_right (by omega) ha
  have hpowB : (n + 1) ^ e ≤ B := by
    simpa only [one_mul] using Nat.mul_le_mul_right ((n + 1) ^ e) hA
  have hbase : n + 1 ≤ B := by
    calc
      n + 1 = (n + 1) ^ 1 := by simp
      _ ≤ (n + 1) ^ e := hpow 1 (by dsimp [e]; omega)
      _ ≤ B := hpowB
  have hprime : p n ≤ n + 1 := (p_le_n hn).trans (Nat.le_succ n)
  have hD : D n ≤ B := (D_le_n hn).trans ((Nat.le_succ n).trans hbase)
  have hQ : SubexponentialSAT.SubexpSchedule.Q n ≤ B := by
    calc
      _ ≤ p n ^ 4 := Q_le_p_pow_four n
      _ ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left hprime 4
      _ ≤ (n + 1) ^ e := hpow 4 (by dsimp [e]; omega)
      _ ≤ B := hpowB
  have hR : SubexponentialSAT.SubexpSchedule.R k hk n ≤ B := (R_le_Q k hk n).trans hQ
  have hfour : 4 ≤ B := by
    have ha : 4 ≤ A := by dsimp [A]; omega
    exact ha.trans (by simpa only [mul_one] using Nat.mul_le_mul_left A hp)
  have hC : C ≤ A := by dsimp [A]; omega
  have hdeltaB : SubexponentialSAT.SubexpSchedule.delta k hk n ≤ B :=
    hdelta.trans (Nat.mul_le_mul hC (hpow d (by dsimp [e]; omega)))
  have hmB : m ≤ B := by
    calc
      m ≤ SubexponentialSAT.SubexpSchedule.delta k hk n * D n := hm
      _ ≤ (C * (n + 1) ^ d) * (n + 1) :=
        Nat.mul_le_mul hdelta ((D_le_n hn).trans (Nat.le_succ n))
      _ = C * (n + 1) ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ A * (n + 1) ^ e :=
        Nat.mul_le_mul hC (hpow (d + 1) (by dsimp [e]; omega))
  have hr : r n ≤ B := (s_le_n n).trans ((Nat.le_succ n).trans hbase)
  have hpk : p n ^ k ≤ B := by
    calc
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_left hprime k
      _ ≤ (n + 1) ^ e := hpow k (by dsimp [e]; omega)
      _ ≤ B := hpowB
  have hkB : k ≤ B := by
    have ha : k ≤ A := by dsimp [A]; omega
    exact ha.trans (by simpa only [mul_one] using Nat.mul_le_mul_left A hp)
  have hlog : Nat.log2 (p n) ≤ B := (Nat.log2_le_self _).trans (hprime.trans hbase)
  have hN : SubexponentialSAT.SubexpSchedule.N k hk n ≤ B :=
    hblock.trans ((Nat.le_succ n).trans hbase)
  intro x hx
  change x ∈ [D n, SubexponentialSAT.SubexpSchedule.Q n, SubexponentialSAT.SubexpSchedule.R k hk n,
    4, m, r n, p n ^ k, k, Nat.log2 (p n),
    SubexponentialSAT.SubexpSchedule.delta k hk n, SubexponentialSAT.SubexpSchedule.N k hk n] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD
  · exact hQ
  · exact hR
  · exact hfour
  · exact hmB
  · exact hr
  · exact hpk
  · exact hkB
  · exact hlog
  · exact hdeltaB
  · exact hN

/-- The concrete schedule has a uniform polynomial bound on all eleven
entries. Coefficient and degree depend only on the fixed width k, and the
eventual threshold is uniform over all permitted leaf factor counts m. -/
theorem eventually_entries_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ C d : ℕ, 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
        m ≤ SubexponentialSAT.SubexpSchedule.delta k hk n * D n →
        ∀ x ∈ (parameters k hk n m).entries, x ≤ C * (n + 1) ^ d := by
  obtain ⟨C, d, hdelta⟩ := SubexponentialSAT.SubexpSchedule.exists_incidence_bound k hk
  have hd : ∀ᶠ n : ℕ in atTop,
      SubexponentialSAT.SubexpSchedule.delta k hk n ≤ C * (s n + 1) ^ d := by
    filter_upwards [eventually_goodInput] with n hn
    exact hdelta n hn
  have hN : ∀ᶠ n : ℕ in atTop, SubexponentialSAT.SubexpSchedule.N k hk n ≤ n := by
    simpa only [SubexponentialSAT.SubexpSchedule.N, pow_one] using
      SubexponentialSAT.SubexpParameters.blockSize_subpolynomial C d 1
        (SubexponentialSAT.SubexpSchedule.delta k hk) hd
  refine ⟨C + k + 5, d + k + 5, by omega, ?_⟩
  filter_upwards [eventually_goodInput, hd, hN] with n hn hdn hNn m hm
  apply entries_le_of_incidence_block_bounds k hk C d n m hn _ hNn hm
  exact hdn.trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (s_le_n n) 1) d))

/-- The actual aggregate parameter size is eventually bounded by a fixed
input polynomial, uniformly for every leaf m ≤ ΔD. -/
theorem eventually_size_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ C d : ℕ, 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
        m ≤ SubexponentialSAT.SubexpSchedule.delta k hk n * D n →
        (parameters k hk n m).size ≤ C * (n + 1) ^ d := by
  obtain ⟨C, d, hC, hentries⟩ := eventually_entries_polynomial k hk
  refine ⟨12 * C, d, by omega, ?_⟩
  filter_upwards [hentries] with n hn m hm
  have hp : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hB : 1 ≤ C * (n + 1) ^ d :=
    hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((n + 1) ^ d) hC)
  calc
    (parameters k hk n m).size ≤ 12 * (C * (n + 1) ^ d) :=
      SubexponentialSAT.SubexpRuntime.GrowingParameters.size_le hB (hn m hm)
    _ = (12 * C) * (n + 1) ^ d := by ring

/-- Every fixed-degree polynomial factor in Proposition 4.2 remains a fixed
input polynomial after substituting all actual growing parameters. -/
theorem eventually_size_power_polynomial (k : ℕ) (hk : 2 ≤ k) (q : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
        m ≤ SubexponentialSAT.SubexpSchedule.delta k hk n * D n →
        (parameters k hk n m).size ^ q ≤ C * (n + 1) ^ d := by
  obtain ⟨C, d, hC, hsize⟩ := eventually_size_polynomial k hk
  refine ⟨C ^ q, d * q, Nat.one_le_pow _ _ hC, ?_⟩
  filter_upwards [hsize] with n hn m hm
  calc
    (parameters k hk n m).size ^ q ≤ (C * (n + 1) ^ d) ^ q :=
      Nat.pow_le_pow_left (hn m hm) q
    _ = C ^ q * (n + 1) ^ (d * q) := by rw [mul_pow, ← pow_mul]

end SubexponentialSAT.SubexpParameterBounds

end OAI.Algorithms
