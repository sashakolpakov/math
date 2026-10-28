import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationConstants

namespace OAI.Algorithms

/-!
# Quantitative sparsification budgets

The old fixed-budget module is unchanged. This module uses its actual C, L, z
recurrence and proves a quadratic upper bound for a doubling search in the
inverse budget. The bound is deliberately coarser than the manuscript's
inverse-budget times logarithm estimate.
-/

namespace SubexponentialSAT.SparsificationBudget

open Filter
open scoped BigOperators Topology
open SubexponentialSAT.SparsificationConstants

/-- Exact natural-arithmetic test for the reciprocal budget 1/s. -/
def ReciprocalAdmissible (k s M : ℕ) : Prop :=
  2 ≤ M ∧ k ≤ M * C M (k - 1) ∧
    (4 * C M (k - 1) * M) ^ (k * s) ≤ 2 ^ M * k ^ (k * s)

instance (k s M : ℕ) : Decidable (ReciprocalAdmissible k s M) := by
  unfold ReciprocalAdmissible
  infer_instance

theorem exists_controlExponent (k a q : ℕ) :
    ∃ T, 1 ≤ T ∧ k ≤ 2 ^ T ∧
      k * (a + 2 + (q + 1) * (T + 2)) ≤ 2 ^ T := by
  have hp : PolynomialBound (fun T => k * (a + 2 + (q + 1) * (T + 2))) :=
    (polynomialBound_const k).mul
      ((polynomialBound_const (a + 2)).add
        ((polynomialBound_const (q + 1)).mul
          (polynomialBound_id.add (polynomialBound_const 2))))
  obtain ⟨T, hT, hpT⟩ :=
    ((eventually_ge_atTop (max 1 k)).and hp.eventually_le_two_pow).exists
  refine ⟨T, (Nat.le_max_left _ _).trans hT, ?_, hpT⟩
  exact ((Nat.le_max_right _ _).trans hT).trans (Nat.lt_pow_self (by decide)).le

/-- A completely discrete quadratic witness: test a power of two near s². -/
theorem dyadic_witness (k a q T s : ℕ) (hk : 2 ≤ k) (hs : 0 < s)
    (hC : ∀ M, 2 ≤ M → C M (k - 1) ≤ a * M ^ q)
    (hT : 1 ≤ T) (hkT : k ≤ 2 ^ T)
    (hcontrol : k * (a + 2 + (q + 1) * (T + 2)) ≤ 2 ^ T) :
    let e := T + 2 * (Nat.log 2 s + 1)
    ReciprocalAdmissible k s (2 ^ e) ∧
      2 ^ e ≤ (4 * 2 ^ T) * s ^ 2 ∧ e ≤ T + 2 * s := by
  let l := Nat.log 2 s + 1
  let e := T + 2 * l
  have hl : l ≤ s := Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))
  have hslow : s ≤ 2 ^ l := (Nat.lt_pow_succ_log_self (by decide) s).le
  have hsup : 2 ^ l ≤ 2 * s := by
    calc
      2 ^ l = 2 ^ (Nat.log 2 s) * 2 := by rw [show l = Nat.log 2 s + 1 from rfl, pow_succ]
      _ ≤ s * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega))
      _ = 2 * s := by ring
  have he : 1 ≤ e := by dsimp [e]; omega
  have hM : 2 ≤ 2 ^ e := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he
  have hcoeff : 4 * a ≤ 2 ^ (a + 2) := by
    have ha : a ≤ 2 ^ a := (Nat.lt_pow_self (by decide)).le
    calc
      4 * a ≤ 4 * 2 ^ a := Nat.mul_le_mul_left 4 ha
      _ = 2 ^ (a + 2) := by rw [pow_add]; norm_num; ring
  have hbase : 4 * C (2 ^ e) (k - 1) * 2 ^ e ≤
      2 ^ (a + 2 + (q + 1) * e) := by
    calc
      4 * C (2 ^ e) (k - 1) * 2 ^ e ≤
          4 * (a * (2 ^ e) ^ q) * 2 ^ e :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hC _ hM))
      _ = (4 * a) * (2 ^ e) ^ (q + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (a + 2) * (2 ^ e) ^ (q + 1) :=
        Nat.mul_le_mul_right _ hcoeff
      _ = 2 ^ (a + 2 + (q + 1) * e) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm e (q + 1)]
  have hts : T ≤ T * s := Nat.le_mul_of_pos_right _ hs
  have hes : e ≤ (T + 2) * s := by dsimp [e]; nlinarith
  have has : a + 2 ≤ (a + 2) * s := Nat.le_mul_of_pos_right _ hs
  have hexpbase : a + 2 + (q + 1) * e ≤
      (a + 2 + (q + 1) * (T + 2)) * s := by
    have := Nat.mul_le_mul_left (q + 1) hes
    nlinarith
  have hexp : (a + 2 + (q + 1) * e) * (k * s) ≤ 2 ^ e := by
    calc
      (a + 2 + (q + 1) * e) * (k * s) ≤
          ((a + 2 + (q + 1) * (T + 2)) * s) * (k * s) :=
        Nat.mul_le_mul_right _ hexpbase
      _ = (k * (a + 2 + (q + 1) * (T + 2))) * s ^ 2 := by ring
      _ ≤ 2 ^ T * s ^ 2 := Nat.mul_le_mul_right _ hcontrol
      _ ≤ 2 ^ T * (2 ^ l) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hslow 2)
      _ = 2 ^ e := by dsimp [e]; rw [← pow_mul, ← pow_add]; congr 1; omega
  have hstrong : (4 * C (2 ^ e) (k - 1) * 2 ^ e) ^ (k * s) ≤ 2 ^ (2 ^ e) := by
    calc
      _ ≤ (2 ^ (a + 2 + (q + 1) * e)) ^ (k * s) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((a + 2 + (q + 1) * e) * (k * s)) :=
        (pow_mul 2 (a + 2 + (q + 1) * e) (k * s)).symm
      _ ≤ 2 ^ (2 ^ e) := Nat.pow_le_pow_right (by decide) hexp
  have hlargeC := four_le_C (2 ^ e) (k - 1) (by omega)
  have hTk : 2 ^ T ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  have hratio : k ≤ 2 ^ e * C (2 ^ e) (k - 1) := by
    have hkM := hkT.trans hTk
    nlinarith
  have hpower : (4 * C (2 ^ e) (k - 1) * 2 ^ e) ^ (k * s) ≤
      2 ^ (2 ^ e) * k ^ (k * s) := by
    exact hstrong.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  refine ⟨⟨hM, hratio, hpower⟩, ?_, ?_⟩
  · calc
      2 ^ e = 2 ^ T * (2 ^ l) ^ 2 := by
        dsimp [e]; rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ T * (2 * s) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsup 2)
      _ = (4 * 2 ^ T) * s ^ 2 := by ring
  · omega

/-- The constants K and T depend only on k, not on the inverse budget s. -/
theorem exists_quantitative_witness (k : ℕ) (hk : 2 ≤ k) :
    ∃ K T : ℕ, ∀ s, 0 < s →
      ∃ e, ReciprocalAdmissible k s (2 ^ e) ∧
        2 ^ e ≤ K * s ^ 2 ∧ e ≤ T + 2 * s := by
  obtain ⟨a, q, hC⟩ := C_polynomialBound (k - 1)
  obtain ⟨T, hT, hkT, hcontrol⟩ := exists_controlExponent k a q
  refine ⟨4 * 2 ^ T, T, ?_⟩
  intro s hs
  exact ⟨T + 2 * (Nat.log 2 s + 1), dyadic_witness k a q T s hk hs hC hT hkT hcontrol⟩

theorem exists_doubling_index (k : ℕ) (hk : 2 ≤ k) (s : ℕ) :
    ∃ e, decide (ReciprocalAdmissible k (max 1 s) (2 ^ e)) = true := by
  obtain ⟨K, T, hw⟩ := exists_quantitative_witness k hk
  obtain ⟨e, he, _, _⟩ := hw (max 1 s) (by omega)
  exact ⟨e, by simpa using he⟩

/-- The least passing doubling index; the candidate at index e is 2^e.
The candidate 1 is harmlessly rejected by the test's M ≥ 2 condition. -/
def chooseExponent (k : ℕ) (hk : 2 ≤ k) (s : ℕ) : ℕ :=
  SubexponentialSAT.ParameterOrder.select
    (fun e => decide (ReciprocalAdmissible k (max 1 s) (2 ^ e)))
    (exists_doubling_index k hk s)

def chooseM (k : ℕ) (hk : 2 ≤ k) (s : ℕ) : ℕ :=
  2 ^ chooseExponent k hk s

theorem chooseM_spec_normalized (k : ℕ) (hk : 2 ≤ k) (s : ℕ) :
    ReciprocalAdmissible k (max 1 s) (chooseM k hk s) := by
  have h := SubexponentialSAT.ParameterOrder.select_spec
    (fun e => decide (ReciprocalAdmissible k (max 1 s) (2 ^ e)))
    (exists_doubling_index k hk s)
  exact of_decide_eq_true h

theorem chooseM_spec (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (hs : 0 < s) :
    ReciprocalAdmissible k s (chooseM k hk s) := by
  simpa [max_eq_right (show 1 ≤ s by omega)] using chooseM_spec_normalized k hk s

theorem chooseM_ge_two (k : ℕ) (hk : 2 ≤ k) (s : ℕ) : 2 ≤ chooseM k hk s :=
  (chooseM_spec_normalized k hk s).1

theorem chooseExponent_le (k : ℕ) (hk : 2 ≤ k) (s e : ℕ)
    (he : ReciprocalAdmissible k (max 1 s) (2 ^ e)) :
    chooseExponent k hk s ≤ e :=
  SubexponentialSAT.ParameterOrder.select_le _ _ (by simpa using he)

theorem chooseM_quadratic_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ K T : ℕ, ∀ s, 0 < s →
      chooseM k hk s ≤ K * s ^ 2 ∧ chooseExponent k hk s ≤ T + 2 * s := by
  obtain ⟨K, T, hw⟩ := exists_quantitative_witness k hk
  refine ⟨K, T, ?_⟩
  intro s hs
  obtain ⟨e, he, hsize, hindex⟩ := hw s hs
  have he' : ReciprocalAdmissible k (max 1 s) (2 ^ e) := by
    simpa [max_eq_right (show 1 ≤ s by omega)] using he
  have hle := chooseExponent_le k hk s e he'
  exact ⟨(Nat.pow_le_pow_right (by decide) hle).trans hsize, hle.trans hindex⟩

theorem chooseM_polynomialBound (k : ℕ) (hk : 2 ≤ k) :
    PolynomialBound (chooseM k hk) := by
  obtain ⟨K, T, h⟩ := chooseM_quadratic_bound k hk
  exact ⟨K, 2, fun s hs => (h s (by omega)).1⟩

/-- The scan tests doubling candidates, and its call count is bounded above. -/
theorem chooseM_finite_execution (k : ℕ) (hk : 2 ≤ k) (s : ℕ) :
    (SubexponentialSAT.ParameterOrder.scanFrom
      (fun e => decide (ReciprocalAdmissible k (max 1 s) (2 ^ e)))
      0 (chooseExponent k hk s + 1)).1 = some (chooseExponent k hk s) ∧
    (SubexponentialSAT.ParameterOrder.scanFrom
      (fun e => decide (ReciprocalAdmissible k (max 1 s) (2 ^ e)))
      0 (chooseExponent k hk s + 1)).2 ≤ chooseExponent k hk s + 1 := by
  unfold chooseExponent
  exact SubexponentialSAT.ParameterOrder.select_finite_execution _ _

theorem ReciprocalAdmissible.ratio_le {k s M : ℕ}
    (h : ReciprocalAdmissible k s M) :
    (k : ℝ) / M ≤ C M (k - 1) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by have := h.1; omega)
  rw [div_le_iff₀ hM]
  exact_mod_cast (by simpa [mul_comm] using h.2.1)

theorem ReciprocalAdmissible.log_budget {k s M : ℕ}
    (h : ReciprocalAdmissible k s M) (hk : 2 ≤ k) (hs : 0 < s) :
    (k : ℝ) / M * Real.log (4 * (C M (k - 1) : ℝ) * M / k) ≤
      Real.log 2 / s := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by have := h.1; omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hCpos : (0 : ℝ) < C M (k - 1) := by
    have := four_le_C M (k - 1) (by omega)
    exact_mod_cast (show 0 < C M (k - 1) by omega)
  have ha : 0 < 4 * (C M (k - 1) : ℝ) * M := by positivity
  have hpower :
      (4 * (C M (k - 1) : ℝ) * M) ^ (k * s) ≤
        (2 : ℝ) ^ M * (k : ℝ) ^ (k * s) := by
    exact_mod_cast h.2.2
  have hlog := Real.log_le_log (pow_pos ha (k * s)) hpower
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow, Nat.cast_mul] at hlog
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hkpos)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  have hd : (k : ℝ) * (Real.log (4 * (C M (k - 1) : ℝ) * M) - Real.log k) ≤
      (M * Real.log 2) / s := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hd

theorem ReciprocalAdmissible.logb_budget {k s M : ℕ}
    (h : ReciprocalAdmissible k s M) (hk : 2 ≤ k) (hs : 0 < s) :
    (k : ℝ) / M * Real.logb 2 (4 * (C M (k - 1) : ℝ) * M / k) ≤
      (1 : ℝ) / s := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, ← mul_div_assoc, div_le_iff₀ htwo]
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h.log_budget hk hs

theorem polynomialBound_comp {f g : ℕ → ℕ} (hf : PolynomialBound f)
    (hg : PolynomialBound g) (hge : ∀ s, 2 ≤ s → 2 ≤ g s) :
    PolynomialBound (fun s => f (g s)) := by
  obtain ⟨a, p, hf⟩ := hf
  obtain ⟨b, q, hg⟩ := hg
  refine ⟨a * b ^ p, q * p, ?_⟩
  intro s hs
  calc
    f (g s) ≤ a * (g s) ^ p := hf _ (hge s hs)
    _ ≤ a * (b * s ^ q) ^ p := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hg s hs) _)
    _ = (a * b ^ p) * s ^ (q * p) := by rw [mul_pow, pow_mul]; ring

theorem polynomialBound_finset_sum {α : Type*} (S : Finset α) (f : α → ℕ → ℕ)
    (hf : ∀ i ∈ S, PolynomialBound (f i)) :
    PolynomialBound (fun s => ∑ i ∈ S, f i s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using polynomialBound_const 0
  | @insert i S hi ih =>
      have hi' := hf i (Finset.mem_insert_self _ _)
      have hS := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hi'.add hS

theorem L_polynomialBound (j : ℕ) : PolynomialBound (fun M => L M j) := by
  cases j with
  | zero => simpa using polynomialBound_const 0
  | succ j =>
      cases j with
      | zero => simpa using polynomialBound_const 1
      | succ j =>
          exact (polynomialBound_const (j + 1).factorial).mul
            (((polynomialBound_id.mul (C_polynomialBound (j + 1))).sub_const 1).pow (j + 1))

theorem z_polynomialBound (d : ℕ) : PolynomialBound (fun M => z M d) :=
  polynomialBound_id.mul (C_polynomialBound (d - 1))

theorem occurrenceCap_polynomialBound (k : ℕ) :
    PolynomialBound (fun M => occurrenceCap M k) :=
  (polynomialBound_const 2).mul
    (polynomialBound_finset_sum (Finset.range (k + 1)) (fun j M => L M j)
      (fun j _ => L_polynomialBound j))

/-- A polynomial cap on every threshold through width k. -/
def thresholdCap (M k : ℕ) : ℕ := ∑ d ∈ Finset.range (k + 1), z M d

theorem z_le_thresholdCap (M k d : ℕ) (hd : d ≤ k) : z M d ≤ thresholdCap M k := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (z M i))
    (Finset.mem_range.mpr (by omega))

theorem thresholdCap_polynomialBound (k : ℕ) :
    PolynomialBound (fun M => thresholdCap M k) :=
  polynomialBound_finset_sum (Finset.range (k + 1)) (fun d M => z M d)
    (fun d _ => z_polynomialBound d)

theorem chosenC_polynomialBound (k : ℕ) (hk : 2 ≤ k) (j : ℕ) :
    PolynomialBound (fun s => C (chooseM k hk s) j) :=
  polynomialBound_comp (C_polynomialBound j) (chooseM_polynomialBound k hk)
    (fun s _ => chooseM_ge_two k hk s)

theorem chosenL_polynomialBound (k : ℕ) (hk : 2 ≤ k) (j : ℕ) :
    PolynomialBound (fun s => L (chooseM k hk s) j) :=
  polynomialBound_comp (L_polynomialBound j) (chooseM_polynomialBound k hk)
    (fun s _ => chooseM_ge_two k hk s)

theorem chosenz_polynomialBound (k : ℕ) (hk : 2 ≤ k) (d : ℕ) :
    PolynomialBound (fun s => z (chooseM k hk s) d) :=
  polynomialBound_comp (z_polynomialBound d) (chooseM_polynomialBound k hk)
    (fun s _ => chooseM_ge_two k hk s)

theorem chosenOccurrenceCap_polynomialBound (k : ℕ) (hk : 2 ≤ k) :
    PolynomialBound (fun s => occurrenceCap (chooseM k hk s) k) :=
  polynomialBound_comp (f := fun M => occurrenceCap M k) (g := chooseM k hk)
    (occurrenceCap_polynomialBound k) (chooseM_polynomialBound k hk)
    (fun s _ => chooseM_ge_two k hk s)

theorem chosenThresholdCap_polynomialBound (k : ℕ) (hk : 2 ≤ k) :
    PolynomialBound (fun s => thresholdCap (chooseM k hk s) k) :=
  polynomialBound_comp (thresholdCap_polynomialBound k) (chooseM_polynomialBound k hk)
    (fun s _ => chooseM_ge_two k hk s)

/-- Conservative reciprocal rounding for a positive rational a/b ≤ 1.
This is ceil(b/a), with a minimum of two. Only the rounded index appears in
the exponents used by the doubling search. -/
def reciprocalIndex (a b : ℕ) : ℕ :=
  max 2 ((b - 1) / a + 1)

theorem reciprocalIndex_ge_two (a b : ℕ) : 2 ≤ reciprocalIndex a b :=
  Nat.le_max_left _ _

theorem reciprocalIndex_mul (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    b ≤ a * reciprocalIndex a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hceil : b ≤ a * ((b - 1) / a + 1) := by
    have h := Nat.lt_mul_div_succ (b - 1) ha
    omega
  exact hceil.trans (Nat.mul_le_mul_left a (Nat.le_max_right _ _))

theorem reciprocalIndex_budget (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (1 : ℝ) / reciprocalIndex a b ≤ (a : ℝ) / b := by
  have hs : (0 : ℝ) < reciprocalIndex a b := by
    exact_mod_cast (show 0 < reciprocalIndex a b from
      lt_of_lt_of_le (by decide) (reciprocalIndex_ge_two a b))
  have hb : (0 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le ha hab
  apply (div_le_div_iff₀ hs hb).mpr
  simpa using (show (b : ℝ) ≤ (a : ℝ) * reciprocalIndex a b by
    exact_mod_cast reciprocalIndex_mul a b ha hab)

theorem reciprocalIndex_le_inverse_add_two (a b : ℕ) (ha : 0 < a) :
    (reciprocalIndex a b : ℝ) ≤ (b : ℝ) / a + 2 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hq : (((b - 1) / a : ℕ) : ℝ) ≤ (b : ℝ) / a := by
    apply (le_div_iff₀ ha').mpr
    exact_mod_cast (Nat.div_mul_le_self (b - 1) a).trans (Nat.sub_le b 1)
  have hb : (0 : ℝ) ≤ (b : ℝ) / a := div_nonneg (Nat.cast_nonneg _) (le_of_lt ha')
  unfold reciprocalIndex
  rw [Nat.cast_max]
  apply max_le
  · norm_num
    linarith
  · push_cast
    linarith

theorem reciprocalIndex_one (s : ℕ) (hs : 2 ≤ s) : reciprocalIndex 1 s = s := by
  simp [reciprocalIndex, Nat.sub_add_cancel (show 1 ≤ s by omega), max_eq_right hs]

def chooseRationalM (k : ℕ) (hk : 2 ≤ k) (a b : ℕ) : ℕ :=
  chooseM k hk (reciprocalIndex a b)

theorem chooseRationalM_logb_budget (k : ℕ) (hk : 2 ≤ k) (a b : ℕ)
    (ha : 0 < a) (hab : a ≤ b) :
    (k : ℝ) / chooseRationalM k hk a b *
      Real.logb 2 (4 * (C (chooseRationalM k hk a b) (k - 1) : ℝ) *
        chooseRationalM k hk a b / k) ≤ (a : ℝ) / b := by
  have hs : 0 < reciprocalIndex a b := by have := reciprocalIndex_ge_two a b; omega
  exact ((chooseM_spec k hk _ hs).logb_budget hk hs).trans
    (reciprocalIndex_budget a b ha hab)

/-- Every polynomial bound in the rounded inverse index becomes a polynomial
bound in the real reciprocal budget, uniformly in the numerator and denominator. -/
theorem polynomialBound_at_reciprocalIndex {f : ℕ → ℕ} (hf : PolynomialBound f) :
    ∃ A q : ℕ, ∀ a b, 0 < a →
      (f (reciprocalIndex a b) : ℝ) ≤
        (A : ℝ) * ((b : ℝ) / a + 2) ^ q := by
  obtain ⟨A, q, hf⟩ := hf
  refine ⟨A, q, ?_⟩
  intro a b ha
  have hidx := reciprocalIndex_le_inverse_add_two a b ha
  have hp : (reciprocalIndex a b : ℝ) ^ q ≤ ((b : ℝ) / a + 2) ^ q :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hidx q
  calc
    (f (reciprocalIndex a b) : ℝ) ≤ (A : ℝ) * (reciprocalIndex a b : ℝ) ^ q := by
      exact_mod_cast hf _ (reciprocalIndex_ge_two a b)
    _ ≤ (A : ℝ) * ((b : ℝ) / a + 2) ^ q :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)

theorem chooseRationalM_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ a b, 0 < a →
      (chooseRationalM k hk a b : ℝ) ≤
        (A : ℝ) * ((b : ℝ) / a + 2) ^ q :=
  polynomialBound_at_reciprocalIndex (chooseM_polynomialBound k hk)

theorem rationalOccurrenceCap_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ a b, 0 < a →
      (occurrenceCap (chooseRationalM k hk a b) k : ℝ) ≤
        (A : ℝ) * ((b : ℝ) / a + 2) ^ q :=
  polynomialBound_at_reciprocalIndex (chosenOccurrenceCap_polynomialBound k hk)

theorem rationalThresholdCap_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ a b, 0 < a →
      (thresholdCap (chooseRationalM k hk a b) k : ℝ) ≤
        (A : ℝ) * ((b : ℝ) / a + 2) ^ q :=
  polynomialBound_at_reciprocalIndex (chosenThresholdCap_polynomialBound k hk)

/-- Positive rationals supply the positive natural numerator used by rounding. -/
theorem rational_num_data (σ : ℚ) (hσ : 0 < σ) :
    0 < σ.num.natAbs ∧
      (σ.num.natAbs : ℝ) / σ.den = (σ : ℝ) := by
  have hnum : 0 < σ.num := Rat.num_pos.mpr hσ
  have habs : (σ.num.natAbs : ℤ) = σ.num := Int.natAbs_of_nonneg (le_of_lt hnum)
  refine ⟨Int.natAbs_pos.mpr (ne_of_gt hnum), ?_⟩
  rw [Rat.cast_def]
  congr 1
  simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) habs

theorem rational_num_le_den (σ : ℚ) (hσ : 0 < σ) (hσone : σ ≤ 1) :
    σ.num.natAbs ≤ σ.den := by
  have hdata := rational_num_data σ hσ
  have hreal : (σ : ℝ) ≤ 1 := by exact_mod_cast hσone
  have hden : (0 : ℝ) < σ.den := by exact_mod_cast σ.pos
  rw [← hdata.2, div_le_one hden] at hreal
  exact_mod_cast hreal

/-- The complete selector accepts a rational budget directly. Numerator and
denominator are inspected only to compute the small reciprocal index. -/
def chooseForSigma (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) : ℕ :=
  chooseRationalM k hk σ.num.natAbs σ.den

theorem chooseForSigma_ge_two (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) :
    2 ≤ chooseForSigma k hk σ :=
  chooseM_ge_two k hk _

theorem chooseForSigma_ratio_le (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) :
    (k : ℝ) / chooseForSigma k hk σ ≤ C (chooseForSigma k hk σ) (k - 1) :=
  (chooseM_spec_normalized k hk _).ratio_le

theorem chooseForSigma_logb_budget (k : ℕ) (hk : 2 ≤ k)
    (σ : ℚ) (hσ : 0 < σ) (hσone : σ ≤ 1) :
    (k : ℝ) / chooseForSigma k hk σ *
      Real.logb 2 (4 * (C (chooseForSigma k hk σ) (k - 1) : ℝ) *
        chooseForSigma k hk σ / k) ≤ (σ : ℝ) := by
  have hdata := rational_num_data σ hσ
  have h := chooseRationalM_logb_budget k hk σ.num.natAbs σ.den hdata.1
    (rational_num_le_den σ hσ hσone)
  simpa only [chooseForSigma, hdata.2] using h

/-- A generic polynomial bound transported to the reciprocal of a rational.
Its witnesses are independent of the numerator and denominator. -/
theorem polynomialBound_at_sigma {f : ℕ → ℕ} (hf : PolynomialBound f) :
    ∃ A q : ℕ, ∀ σ : ℚ, 0 < σ →
      (f (reciprocalIndex σ.num.natAbs σ.den) : ℝ) ≤
        (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q := by
  obtain ⟨A, q, h⟩ := polynomialBound_at_reciprocalIndex hf
  refine ⟨A, q, ?_⟩
  intro σ hσ
  have hdata := rational_num_data σ hσ
  have hinv : (σ.den : ℝ) / σ.num.natAbs = (σ : ℝ)⁻¹ := by
    rw [← hdata.2, inv_div]
  simpa only [hinv] using h σ.num.natAbs σ.den hdata.1

theorem chooseForSigma_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ σ : ℚ, 0 < σ →
      (chooseForSigma k hk σ : ℝ) ≤ (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q :=
  polynomialBound_at_sigma (chooseM_polynomialBound k hk)

theorem chooseForSigma_quadratic_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ K : ℕ, ∀ σ : ℚ, 0 < σ →
      (chooseForSigma k hk σ : ℝ) ≤ (K : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ 2 := by
  obtain ⟨K, T, hK⟩ := chooseM_quadratic_bound k hk
  refine ⟨K, ?_⟩
  intro σ hσ
  have hdata := rational_num_data σ hσ
  have hinv : (σ.den : ℝ) / σ.num.natAbs = (σ : ℝ)⁻¹ := by
    rw [← hdata.2, inv_div]
  have hidx := reciprocalIndex_le_inverse_add_two σ.num.natAbs σ.den hdata.1
  rw [hinv] at hidx
  have htwo := reciprocalIndex_ge_two σ.num.natAbs σ.den
  have hM := (hK (reciprocalIndex σ.num.natAbs σ.den) (by omega)).1
  have hp := pow_le_pow_left₀
    (Nat.cast_nonneg (reciprocalIndex σ.num.natAbs σ.den)) hidx 2
  calc
    (chooseForSigma k hk σ : ℝ) ≤
        (K : ℝ) * (reciprocalIndex σ.num.natAbs σ.den : ℝ) ^ 2 := by
      exact_mod_cast hM
    _ ≤ (K : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg K)

theorem sigmaOccurrenceCap_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ σ : ℚ, 0 < σ →
      (occurrenceCap (chooseForSigma k hk σ) k : ℝ) ≤
        (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q :=
  polynomialBound_at_sigma (chosenOccurrenceCap_polynomialBound k hk)

theorem sigmaThresholdCap_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ σ : ℚ, 0 < σ →
      (thresholdCap (chooseForSigma k hk σ) k : ℝ) ≤
        (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q :=
  polynomialBound_at_sigma (chosenThresholdCap_polynomialBound k hk)

end SubexponentialSAT.SparsificationBudget

end OAI.Algorithms
