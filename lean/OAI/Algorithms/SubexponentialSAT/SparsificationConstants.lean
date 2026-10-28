import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ParameterOrder

namespace OAI.Algorithms

/-!
# The constants in the sparsification argument

The definitions below follow Appendix A.3. The polynomial growth bound is an
explicit existential bound by a natural monomial. It is independent of the
formula size. The final admissibility predicate uses only decidable natural
arithmetic, so it can be fed to an effective least-number search.
-/

namespace SubexponentialSAT.SparsificationConstants

open Filter
open scoped BigOperators Topology

/-- Cumulative insertion constant through width j. -/
def C (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 4
  | j + 2 =>
      C M (j + 1) +
        ((j + 1).factorial * (M * C M (j + 1) - 1) ^ (j + 1) + 1) *
          (2 + C M (j + 1))

/-- The per-literal occurrence bound at width j. Width zero is unused. -/
def L (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | j + 2 => (j + 1).factorial * (M * C M (j + 1) - 1) ^ (j + 1)

/-- The chosen sunflower threshold at width d ≥ 2. -/
def z (M d : ℕ) : ℕ := M * C M (d - 1)

/-- Final per-variable clause-occurrence cap. The width-zero summand is zero. -/
def occurrenceCap (M k : ℕ) : ℕ :=
  2 * ∑ j ∈ Finset.range (k + 1), L M j

@[simp] theorem C_zero (M : ℕ) : C M 0 = 0 := rfl
@[simp] theorem C_one (M : ℕ) : C M 1 = 4 := rfl
@[simp] theorem L_zero (M : ℕ) : L M 0 = 0 := rfl
@[simp] theorem L_one (M : ℕ) : L M 1 = 1 := rfl

@[simp] theorem occurrenceCap_zero (M : ℕ) : occurrenceCap M 0 = 0 := by
  simp [occurrenceCap]

theorem occurrenceCap_succ (M k : ℕ) :
    occurrenceCap M (k + 1) = occurrenceCap M k + 2 * L M (k + 1) := by
  simp only [occurrenceCap, Finset.sum_range_succ]
  ring

theorem C_succ (M j : ℕ) :
    C M (j + 1) = C M j + (L M (j + 1) + 1) * (2 + C M j) := by
  cases j <;> simp [C, L]

theorem C_add_two (M j : ℕ) :
    C M (j + 1) + 2 = (L M (j + 1) + 2) * (C M j + 2) := by
  rw [C_succ]
  ring

theorem C_monotone (M : ℕ) : Monotone (C M) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [C_succ]
  omega

theorem four_le_C (M j : ℕ) (hj : 1 ≤ j) : 4 ≤ C M j := by
  simpa using C_monotone M hj

theorem threshold_ge_two (M d : ℕ) (hM : 2 ≤ M) (hd : 2 ≤ d) :
    2 ≤ z M d := by
  have hC := four_le_C M (d - 1) (by omega)
  unfold z
  nlinarith

theorem L_eq_threshold_formula (M d : ℕ) (hd : 2 ≤ d) :
    L M d = (d - 1).factorial * (z M d - 1) ^ (d - 1) := by
  cases d with
  | zero => omega
  | succ d =>
      cases d with
      | zero => omega
      | succ d => simp [L, z]

/-- The finite-width version needs charging inequalities only through j. -/
theorem cumulative_insertions_le_bounded (M n : ℕ) (N : ℕ → ℕ) (hzero : N 0 = 0) :
    ∀ j, (∀ i, 1 ≤ i → i ≤ j →
      N i ≤ (L M i + 1) * (2 * n + ∑ a ∈ Finset.range i, N a)) →
      (∑ i ∈ Finset.range (j + 1), N i) ≤ C M j * n := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [hzero]
  | succ j ih =>
      intro hcharge
      have hprev := ih (fun i hi hij => hcharge i hi (by omega))
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range (j + 1), N i) + N (j + 1)
            ≤ C M j * n + (L M (j + 1) + 1) * (2 * n + C M j * n) := by
              apply Nat.add_le_add hprev
              exact (hcharge (j + 1) (by omega) le_rfl).trans
                (Nat.mul_le_mul_left _ (Nat.add_le_add_left hprev _))
        _ = C M (j + 1) * n := by rw [C_succ]; ring

/-- Equation (A.1) implies the cumulative insertion bound. The zero-width
count is zero; the sum includes it to match the charging interface. -/
theorem cumulative_insertions_le (M n : ℕ) (N : ℕ → ℕ) (hzero : N 0 = 0)
    (hcharge : ∀ j, 1 ≤ j →
      N j ≤ (L M j + 1) * (2 * n + ∑ i ∈ Finset.range j, N i)) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), N i) ≤ C M j * n := by
  induction j with
  | zero => simp [hzero]
  | succ j ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range (j + 1), N i) + N (j + 1)
            ≤ C M j * n + (L M (j + 1) + 1) * (2 * n + C M j * n) := by
              apply Nat.add_le_add ih
              exact (hcharge (j + 1) (by omega)).trans
                (Nat.mul_le_mul_left _ (Nat.add_le_add_left ih _))
        _ = C M (j + 1) * n := by rw [C_succ]; ring

/-- The integral per-width B-choice bound from the cumulative insertion budget. -/
theorem B_choices_mul_le (M d n b : ℕ) (hd : 2 ≤ d)
    (hinsert : b * z M d ≤ C M (d - 1) * n) :
    b * M ≤ n := by
  have hC : 0 < C M (d - 1) := by
    have := four_le_C M (d - 1) (by omega)
    omega
  have h : C M (d - 1) * (b * M) ≤ C M (d - 1) * n := by
    simpa [z, mul_assoc, mul_comm, mul_left_comm] using hinsert
  exact Nat.le_of_mul_le_mul_left h hC

theorem B_choices_le_div (M d n b : ℕ) (hM : 0 < M) (hd : 2 ≤ d)
    (hinsert : b * z M d ≤ C M (d - 1) * n) :
    b ≤ n / M := by
  exact (Nat.le_div_iff_mul_le hM).mpr (B_choices_mul_le M d n b hd hinsert)

/-- Summing the per-width budgets retains an integral total-choice bound. -/
theorem B_choices_sum_mul_le (M n : ℕ) (s : Finset ℕ) (b : ℕ → ℕ)
    (hwidth : ∀ d ∈ s, 2 ≤ d)
    (hinsert : ∀ d ∈ s, b d * z M d ≤ C M (d - 1) * n) :
    (∑ d ∈ s, b d) * M ≤ s.card * n := by
  have h := Finset.sum_le_sum (fun d hd =>
    B_choices_mul_le M d n (b d) (hwidth d hd) (hinsert d hd))
  simpa [Finset.sum_mul] using h

theorem B_choices_sum_le_div (M n : ℕ) (hM : 0 < M) (s : Finset ℕ) (b : ℕ → ℕ)
    (hwidth : ∀ d ∈ s, 2 ≤ d)
    (hinsert : ∀ d ∈ s, b d * z M d ≤ C M (d - 1) * n) :
    (∑ d ∈ s, b d) ≤ s.card * n / M :=
  (Nat.le_div_iff_mul_le hM).mpr (B_choices_sum_mul_le M n s b hwidth hinsert)

/-- Both witnesses depend only on the fixed function, never on M. -/
def PolynomialBound (f : ℕ → ℕ) : Prop :=
  ∃ a q : ℕ, ∀ M, 2 ≤ M → f M ≤ a * M ^ q

theorem polynomialBound_const (a : ℕ) : PolynomialBound (fun _ => a) := by
  exact ⟨a, 0, by simp⟩

theorem polynomialBound_id : PolynomialBound (fun M => M) := by
  exact ⟨1, 1, by simp⟩

theorem PolynomialBound.mono {f g : ℕ → ℕ} (hg : PolynomialBound g)
    (hfg : ∀ M, 2 ≤ M → f M ≤ g M) : PolynomialBound f := by
  obtain ⟨a, q, h⟩ := hg
  exact ⟨a, q, fun M hM => (hfg M hM).trans (h M hM)⟩

theorem PolynomialBound.add {f g : ℕ → ℕ}
    (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun M => f M + g M) := by
  obtain ⟨a, p, hf⟩ := hf
  obtain ⟨b, q, hg⟩ := hg
  refine ⟨a + b, p + q, ?_⟩
  intro M hM
  have hp : M ^ p ≤ M ^ (p + q) := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : M ^ q ≤ M ^ (p + q) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f M + g M ≤ a * M ^ p + b * M ^ q := Nat.add_le_add (hf M hM) (hg M hM)
    _ ≤ a * M ^ (p + q) + b * M ^ (p + q) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)
    _ = (a + b) * M ^ (p + q) := by ring

theorem PolynomialBound.mul {f g : ℕ → ℕ}
    (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun M => f M * g M) := by
  obtain ⟨a, p, hf⟩ := hf
  obtain ⟨b, q, hg⟩ := hg
  refine ⟨a * b, p + q, ?_⟩
  intro M hM
  calc
    f M * g M ≤ (a * M ^ p) * (b * M ^ q) := Nat.mul_le_mul (hf M hM) (hg M hM)
    _ = (a * b) * M ^ (p + q) := by rw [pow_add]; ring

theorem PolynomialBound.pow {f : ℕ → ℕ} (hf : PolynomialBound f) (r : ℕ) :
    PolynomialBound (fun M => f M ^ r) := by
  obtain ⟨a, p, hf⟩ := hf
  refine ⟨a ^ r, p * r, ?_⟩
  intro M hM
  calc
    f M ^ r ≤ (a * M ^ p) ^ r := Nat.pow_le_pow_left (hf M hM) r
    _ = a ^ r * M ^ (p * r) := by rw [mul_pow, pow_mul]

theorem PolynomialBound.sub_const {f : ℕ → ℕ} (hf : PolynomialBound f) (a : ℕ) :
    PolynomialBound (fun M => f M - a) :=
  hf.mono (fun _ _ => Nat.sub_le _ _)

theorem C_polynomialBound (j : ℕ) : PolynomialBound (fun M => C M j) := by
  induction j with
  | zero => simpa using polynomialBound_const 0
  | succ j ih =>
      cases j with
      | zero => simpa using polynomialBound_const 4
      | succ j =>
          change PolynomialBound (fun M =>
            C M (j + 1) +
              ((j + 1).factorial * (M * C M (j + 1) - 1) ^ (j + 1) + 1) *
                (2 + C M (j + 1)))
          exact ih.add
            (((polynomialBound_const _).mul
              (((polynomialBound_id.mul ih).sub_const 1).pow (j + 1))).add
                (polynomialBound_const 1) |>.mul ((polynomialBound_const 2).add ih))

/-- Fixed polynomial growth is eventually bounded by two to the M. -/
theorem PolynomialBound.eventually_le_two_pow {f : ℕ → ℕ}
    (hf : PolynomialBound f) : ∀ᶠ M in atTop, f M ≤ 2 ^ M := by
  obtain ⟨a, q, hf⟩ := hf
  have ho := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) q
    (by norm_num : (1 : ℝ) < 2)).const_mul_left (a : ℝ)
  have hb := ho.def (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop 2] with M hbound hM
  have hreal : (a : ℝ) * (M : ℝ) ^ q ≤ (2 : ℝ) ^ M := by
    simpa using hbound
  have hnat : a * M ^ q ≤ 2 ^ M := by exact_mod_cast hreal
  exact (hf M hM).trans hnat

/-- Decidable form of the threshold constraints, including (A.2). -/
def Admissible (k M : ℕ) : Prop :=
  2 ≤ M ∧ k ≤ M * C M (k - 1) ∧
    (4 * C M (k - 1) * M) ^ (32 * k) ≤ 2 ^ M * k ^ (32 * k)

instance (k M : ℕ) : Decidable (Admissible k M) := by
  unfold Admissible
  infer_instance

theorem eventually_admissible (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ M in atTop, Admissible k M := by
  have hp : PolynomialBound (fun M => (4 * C M (k - 1) * M) ^ (32 * k)) :=
    (((polynomialBound_const 4).mul (C_polynomialBound (k - 1))).mul
      polynomialBound_id).pow _
  filter_upwards [hp.eventually_le_two_pow, eventually_ge_atTop (max 2 k)]
    with M hp hM
  have htwo : 2 ≤ M := (Nat.le_max_left _ _).trans hM
  have hkM : k ≤ M := (Nat.le_max_right _ _).trans hM
  have hC := four_le_C M (k - 1) (by omega)
  refine ⟨htwo, ?_, ?_⟩
  · nlinarith
  · have hkpow : 1 ≤ k ^ (32 * k) := Nat.one_le_pow _ _ (by omega)
    exact hp.trans (by simpa using Nat.mul_le_mul_left (2 ^ M) hkpow)

theorem exists_admissible (k : ℕ) (hk : 2 ≤ k) : ∃ M, Admissible k M :=
  (eventually_admissible k hk).exists

/-- The integral predicate implies the natural-log form used by tree counting. -/
theorem Admissible.log_budget {k M : ℕ} (h : Admissible k M) (hk : 2 ≤ k) :
    (k : ℝ) / M * Real.log (4 * (C M (k - 1) : ℝ) * M / k) ≤
      Real.log 2 / 32 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by have := h.1; omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hC : (0 : ℝ) < C M (k - 1) := by
    have := four_le_C M (k - 1) (by omega)
    exact_mod_cast (show 0 < C M (k - 1) by omega)
  have ha : 0 < 4 * (C M (k - 1) : ℝ) * M := by positivity
  have hpower :
      (4 * (C M (k - 1) : ℝ) * M) ^ (32 * k) ≤
        (2 : ℝ) ^ M * (k : ℝ) ^ (32 * k) := by
    exact_mod_cast h.2.2
  have hlog := Real.log_le_log (pow_pos ha (32 * k)) hpower
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hlog
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hkpos)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  nlinarith

theorem Admissible.logb_budget {k M : ℕ} (h : Admissible k M) (hk : 2 ≤ k) :
    (k : ℝ) / M * Real.logb 2 (4 * (C M (k - 1) : ℝ) * M / k) ≤
      (1 : ℝ) / 32 := by
  have hlog := h.log_budget hk
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, ← mul_div_assoc, div_le_iff₀ htwo]
  nlinarith

theorem Admissible.ratio_le {k M : ℕ} (h : Admissible k M) :
    (k : ℝ) / M ≤ C M (k - 1) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by have := h.1; omega)
  rw [div_le_iff₀ hM]
  exact_mod_cast (by simpa [mul_comm] using h.2.1)

/-- A decidable, terminating least-parameter search with no input-size argument. -/
def chooseM (k : ℕ) (hk : 2 ≤ k) : ℕ :=
  SubexponentialSAT.ParameterOrder.selectAtTop (fun M => decide (Admissible k M))
    ((eventually_admissible k hk).mono (fun _ h => by simpa using h))

theorem chooseM_spec (k : ℕ) (hk : 2 ≤ k) : Admissible k (chooseM k hk) := by
  have h := SubexponentialSAT.ParameterOrder.selectAtTop_spec
    (fun M => decide (Admissible k M))
    ((eventually_admissible k hk).mono (fun _ h => by simpa using h))
  exact of_decide_eq_true h

/-- The least-number search has a finite execution by the explicit Boolean scan.
The bound counts predicate calls, not bit operations. -/
theorem chooseM_finite_execution (k : ℕ) (hk : 2 ≤ k) :
    (SubexponentialSAT.ParameterOrder.scanFrom (fun M => decide (Admissible k M)) 0
      (chooseM k hk + 1)).1 = some (chooseM k hk) ∧
    (SubexponentialSAT.ParameterOrder.scanFrom (fun M => decide (Admissible k M)) 0
      (chooseM k hk + 1)).2 ≤ chooseM k hk + 1 := by
  unfold chooseM SubexponentialSAT.ParameterOrder.selectAtTop SubexponentialSAT.ParameterOrder.selectEventually
  exact SubexponentialSAT.ParameterOrder.select_finite_execution _ _

theorem chooseM_logb_budget (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) / chooseM k hk *
      Real.logb 2 (4 * (C (chooseM k hk) (k - 1) : ℝ) * chooseM k hk / k) ≤
        (1 : ℝ) / 32 :=
  (chooseM_spec k hk).logb_budget hk

end SubexponentialSAT.SparsificationConstants

end OAI.Algorithms
