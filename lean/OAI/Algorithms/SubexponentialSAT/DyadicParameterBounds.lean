import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicSchedule
import OAI.Algorithms.SubexponentialSAT.SubexpRuntime

namespace OAI.Algorithms

/-!
# Polynomial parameter bounds for the implemented dyadic schedule

First the finite bound is proved for an arbitrary incidence schedule with a
proved polynomial bound. It is then instantiated with DyadicSchedule.delta.
All eleven entries are included, notably the fixed-width power p^k. Constants
are chosen before the input size and uniformly over all leaf factor counts.
-/

namespace SubexponentialSAT.DyadicParameterBounds

open Filter
open SubexponentialSAT.SubexpPackingParameters

/-- The runtime parameter record for any supplied incidence schedule. -/
def parametersOfIncidence (k : ℕ) (δ : ℕ → ℕ) (n m : ℕ) :
    SubexponentialSAT.SubexpRuntime.GrowingParameters where
  D := D n
  Q := SubexpParameters.sizeQ (p n)
  R := SubexpParameters.degreeR (p n) k (δ n)
  h := 4
  m := m
  r := r n
  p := p n
  k := k
  incidence := δ n
  blockSize := SubexpParameters.blockSize (s n) (p n) (δ n)

/-- The actual record, with the fixed dyadic control constant selected before n. -/
def parameters (k T n m : ℕ) : SubexponentialSAT.SubexpRuntime.GrowingParameters :=
  parametersOfIncidence k (DyadicSchedule.delta k T) n m

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

theorem Q_le_p_pow_four (n : ℕ) : SubexpParameters.sizeQ (p n) ≤ p n ^ 4 :=
  Nat.sub_le _ _

theorem R_le_Q (k : ℕ) (δ : ℕ → ℕ) (n : ℕ) :
    SubexpParameters.degreeR (p n) k (δ n) ≤ SubexpParameters.sizeQ (p n) :=
  Nat.div_le_self _ _

/-- A finite simultaneous bound, after only the incidence and block-size
bounds have been supplied. Those two bounds are discharged below from the
actual schedule and the proved subpolynomial block-size theorem. -/
theorem entries_le_of_incidence_block_bounds
    (k : ℕ) (δ : ℕ → ℕ) (C d n m : ℕ)
    (hn : GoodInput n)
    (hdelta : δ n ≤ C * (n + 1) ^ d)
    (hblock : SubexpParameters.blockSize (s n) (p n) (δ n) ≤ n)
    (hm : m ≤ δ n * D n) :
    ∀ x ∈ (parametersOfIncidence k δ n m).entries,
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
  have hQ : SubexpParameters.sizeQ (p n) ≤ B := by
    calc
      _ ≤ p n ^ 4 := Q_le_p_pow_four n
      _ ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left hprime 4
      _ ≤ (n + 1) ^ e := hpow 4 (by dsimp [e]; omega)
      _ ≤ B := hpowB
  have hR : SubexpParameters.degreeR (p n) k (δ n) ≤ B := (R_le_Q k δ n).trans hQ
  have hfour : 4 ≤ B := by
    have ha : 4 ≤ A := by dsimp [A]; omega
    exact ha.trans (by simpa only [mul_one] using Nat.mul_le_mul_left A hp)
  have hC : C ≤ A := by dsimp [A]; omega
  have hdeltaB : δ n ≤ B :=
    hdelta.trans (Nat.mul_le_mul hC (hpow d (by dsimp [e]; omega)))
  have hmB : m ≤ B := by
    calc
      m ≤ δ n * D n := hm
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
  have hN : SubexpParameters.blockSize (s n) (p n) (δ n) ≤ B :=
    hblock.trans ((Nat.le_succ n).trans hbase)
  intro x hx
  change x ∈ [D n, SubexpParameters.sizeQ (p n), SubexpParameters.degreeR (p n) k (δ n),
    4, m, r n, p n ^ k, k, Nat.log2 (p n),
    δ n, SubexpParameters.blockSize (s n) (p n) (δ n)] at hx
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

/-- Generic substitution of a proved polynomial incidence bound. -/
theorem eventually_entries_polynomial_of_incidence (k C d : ℕ) (δ : ℕ → ℕ)
    (hd : ∀ᶠ n : ℕ in atTop, δ n ≤ C * (s n + 1) ^ d) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ δ n * D n →
      ∀ x ∈ (parametersOfIncidence k δ n m).entries,
        x ≤ (C + k + 5) * (n + 1) ^ (d + k + 5) := by
  have hN : ∀ᶠ n : ℕ in atTop,
      SubexpParameters.blockSize (s n) (p n) (δ n) ≤ n := by
    simpa only [pow_one] using
      SubexpParameters.blockSize_subpolynomial C d 1 δ hd
  filter_upwards [eventually_goodInput, hd, hN] with n hn hdn hNn m hm
  apply entries_le_of_incidence_block_bounds k δ C d n m hn _ hNn hm
  exact hdn.trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (s_le_n n) 1) d))

/-- Constants depend only on the fixed width and fixed dyadic control constant. -/
theorem eventually_entries_polynomial (k T : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
        m ≤ DyadicSchedule.delta k T n * D n →
        ∀ x ∈ (parameters k T n m).entries, x ≤ C * (n + 1) ^ d := by
  obtain ⟨C, d, hdelta⟩ := DyadicSchedule.exists_incidence_bound k T
  have hd : ∀ᶠ n : ℕ in atTop,
      DyadicSchedule.delta k T n ≤ C * (s n + 1) ^ d := by
    filter_upwards [eventually_goodInput] with n hn
    exact hdelta n hn
  exact ⟨C + k + 5, d + k + 5, by omega,
    eventually_entries_polynomial_of_incidence k C d (DyadicSchedule.delta k T) hd⟩

/-- The actual aggregate parameter size has one uniform input-polynomial bound. -/
theorem eventually_size_polynomial (k T : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
        m ≤ DyadicSchedule.delta k T n * D n →
        (parameters k T n m).size ≤ C * (n + 1) ^ d := by
  obtain ⟨C, d, hC, hentries⟩ := eventually_entries_polynomial k T
  refine ⟨12 * C, d, by omega, ?_⟩
  filter_upwards [hentries] with n hn m hm
  have hp : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hB : 1 ≤ C * (n + 1) ^ d :=
    hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((n + 1) ^ d) hC)
  calc
    (parameters k T n m).size ≤ 12 * (C * (n + 1) ^ d) :=
      SubexponentialSAT.SubexpRuntime.GrowingParameters.size_le hB (hn m hm)
    _ = (12 * C) * (n + 1) ^ d := by ring

/-- Every fixed power of the aggregate parameter size remains polynomial. -/
theorem eventually_size_power_polynomial (k T q : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
        m ≤ DyadicSchedule.delta k T n * D n →
        (parameters k T n m).size ^ q ≤ C * (n + 1) ^ d := by
  obtain ⟨C, d, hC, hsize⟩ := eventually_size_polynomial k T
  refine ⟨C ^ q, d * q, Nat.one_le_pow _ _ hC, ?_⟩
  filter_upwards [hsize] with n hn m hm
  calc
    (parameters k T n m).size ^ q ≤ (C * (n + 1) ^ d) ^ q :=
      Nat.pow_le_pow_left (hn m hm) q
    _ = C ^ q * (n + 1) ^ (d * q) := by rw [mul_pow, ← pow_mul]

end SubexponentialSAT.DyadicParameterBounds

end OAI.Algorithms
