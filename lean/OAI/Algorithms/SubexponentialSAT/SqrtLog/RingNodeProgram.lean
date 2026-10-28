import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldRowPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationProgram
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-! A fixed physical program generating all nonzero radix nodes up to a runtime
bound. The bound counts down, so prepending each row gives ascending order. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation SubexpBasePUnranking SubexpEnumerationProgram
open BinaryArithmetic SubexpLiftRing

/-- Canonical padded radix digits, least significant coefficient first. -/
def digits (B p : ℕ) : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => fixedBits B (n % p) ++ digits B p k (n / p)

@[simp] theorem digits_length (B p k n : ℕ) : (digits B p k n).length = k * B := by
  induction k generalizing n with
  | zero => simp [digits]
  | succ k ih => simp [digits, ih, Nat.add_mul, Nat.add_comm]

theorem unrank_eq_digits (m rank : List Bool) (hm : 0 < BinaryArithmetic.toNat m) (k : ℕ) :
    (digitWords m k rank).flatten = digits m.length (BinaryArithmetic.toNat m) k (BinaryArithmetic.toNat rank) := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih =>
    have hd : digit m rank = fixedBits m.length (BinaryArithmetic.toNat rank % BinaryArithmetic.toNat m) := by
      apply SubexpModulusConstruction.bits_eq_of_length_of_value
      · simp [digit_length]
      · rw [digit_value m rank hm, toNat_fixedBits_of_lt]
        exact (Nat.mod_lt _ hm).trans (SubexpFactorProgram.toNat_lt_pow_length m)
    simp only [digitWords, List.flatten_cons, digits, hd]
    rw [ih, nextRank_value m rank hm]

/-- Nodes 1 through Q in order. This is a specification, not an instruction. -/
def stream (B p d : ℕ) : ℕ → List Bool
  | 0 => []
  | Q + 1 => stream B p d Q ++ digits B p d (Q + 1)

@[simp] theorem stream_length (B p d Q : ℕ) :
    (stream B p d Q).length = Q * (d * B) := by
  induction Q with
  | zero => simp [stream]
  | succ Q ih => simp [stream, ih, Nat.add_mul]

/-- Only the remaining counter and its scratch are used by this controller. -/
def ports : Ports 8 15 where
  register := ⟨fun i => i.castLE (by decide), by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  current := 6
  remaining := 13
  scratch := 10
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

abbrev step : Cmd 8 15 := .seq SubexpFieldRowPreparation.command
  (.seq (rippleCmd ports false false) (testCmd ports))
abbrev loop : Cmd 8 15 := .while (ports.register 2) step
abbrev command : Cmd 8 15 := .seq (testCmd ports) loop

private theorem test_data (r : Fin 8 → Bool) (m rank arity out : List Bool) :
    testResult ports (data r m rank arity [] [] out) =
      data (testResult ports (data r m rank arity [] [] out)).regs m rank arity [] [] out := by
  apply SubexpEnumerationProgram.data_ext
  · rfl
  · exact testResult_stacks ports _ rfl

private theorem ripple_data (r : Fin 8 → Bool) (m rank arity out : List Bool) :
    rippleResult ports false false (data r m rank arity [] [] out) =
      data (rippleResult ports false false (data r m rank arity [] [] out)).regs
        m (ripple false rank) arity [] [] out := by
  apply SubexpEnumerationProgram.data_ext
  · rfl
  · funext i
    by_cases h13 : i = 13
    · subst i
      exact rippleResult_target ports false false _
    by_cases h10 : i = 10
    · subst i
      exact rippleResult_scratch ports false false _
    rw [rippleResult_other ports false false _ i h13 h10]
    fin_cases i <;> simp_all [data, SubexpFieldRowPreparation.tapes]
/-- One node extraction including binary decrement and the next loop test. -/
def stepBudget (B L d : ℕ) : ℕ :=
  d * (100 * (B + L + 1)^2 + 14*B + 8*L + 19) + 25*L + 7*d + 35

private theorem step_eval (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hp : 0 < value rank) (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ n ≤ stepBudget m.length rank.length arity.length, ∃ rf,
      Eval step n (data r m rank arity [] [] out)
        (data rf m (ripple false rank) arity [] []
          (digits m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out)) ∧
      rf (ports.register 2) = !(isZero (ripple false rank)) := by
  obtain ⟨nb, hb, rb, eb⟩ := SubexpFieldRowPreparation.command_eval r m rank arity out
  rw [unrank_eq_digits m rank hm] at eb
  let out' := digits m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out
  let db := data rb m rank arity [] [] out'
  have ed := ripple_eval ports false false db rfl
  rw [ripple_data] at ed
  let rd := (rippleResult ports false false db).regs
  have et := test_eval ports (data rd m (ripple false rank) arity [] [] out') rfl
  have hf := testResult_flag ports (data rd m (ripple false rank) arity [] [] out')
  rw [test_data] at et
  have h := eb.seq (ed.seq et)
  refine ⟨_, ?_, _, h, hf⟩
  dsimp [db, out'] at *
  have hc := rippleCost_le false rank
  have hl := decrement_length hp
  simp only [ports, target, Bool.false_eq_true, ↓reduceIte, data, tapes_13] at *
  dsimp [stepBudget, SubexpFieldRowPreparation.budget, SubexpBasePUnranking.budget] at *
  omega

private theorem value_eq_toNat (xs : List Bool) : value xs = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp_all [value, BinaryArithmetic.toNat, bitVal]

private theorem loop_eval (Q : ℕ) (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hm : 0 < BinaryArithmetic.toNat m) (hq : value rank = Q)
    (hf : r (ports.register 2) = !(isZero rank)) :
    ∃ n ≤ Q * stepBudget m.length rank.length arity.length + Q + 1, ∃ rf finalRank,
      Eval loop n (data r m rank arity [] [] out)
        (data rf m finalRank arity [] []
          (stream m.length (BinaryArithmetic.toNat m) arity.length Q ++ out)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  induction Q generalizing r rank out with
  | zero =>
    have hz := (isZero_eq_true_iff rank).2 hq
    refine ⟨1, by omega, r, rank, ?_, hq, rfl⟩
    simpa [stream, loop, hz] using (Eval.while_false (body := step)
      (by simpa [SubexpFieldRowPreparation.data, hz] using hf) :
      Eval (.while (ports.register 2) step) 1
        (data r m rank arity [] [] out) (data r m rank arity [] [] out))
  | succ Q ih =>
    have hp : 0 < value rank := by omega
    have hz := (isZero_eq_false_iff rank).2 hp
    obtain ⟨ns, hs, rs, es, fs⟩ := step_eval r m rank arity out hp hm
    have hv := value_decrement hp
    have hl := decrement_length hp
    have hnext : value (ripple false rank) = Q := by omega
    obtain ⟨nl, hlb, rl, last, el, hvlast, hllast⟩ :=
      ih rs (ripple false rank)
        (digits m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out) hnext fs
    refine ⟨ns + nl + 1, ?_, rl, last, ?_, hvlast, hllast.trans hl⟩
    · rw [hl] at hlb
      nlinarith
    · have h := Eval.while_true
        (by simpa [SubexpFieldRowPreparation.data, hz] using hf) es el
      have hr : BinaryArithmetic.toNat rank = Q + 1 := by rw [← value_eq_toNat, hq]
      simpa only [loop, stream, List.append_assoc, hr] using h

/-- Explicit bit-program instruction budget, before the fixed primitive overhead. -/
def budget (B L d Q : ℕ) : ℕ := 8*L + 8 + Q * (stepBudget B L d + 1)

/-- No node table is an input: runtime Q, arity, and a padded positive radix
suffice to physically produce every node record. -/
theorem command_eval (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ n ≤ budget m.length rank.length arity.length (BinaryArithmetic.toNat rank), ∃ rf finalRank,
      Eval command n (data r m rank arity [] [] out)
        (data rf m finalRank arity [] []
          (stream m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  have et := test_eval ports (data r m rank arity [] [] out) rfl
  have hf := testResult_flag ports (data r m rank arity [] [] out)
  rw [test_data] at et
  obtain ⟨nl, hl, rf, last, el, hv, hlen⟩ :=
    loop_eval (BinaryArithmetic.toNat rank) _ m rank arity out hm (value_eq_toNat rank) hf
  refine ⟨_, ?_, rf, last, et.seq el, hv, hlen⟩
  simp only [ports, data, tapes_13]
  dsimp [budget]
  nlinarith

abbrev program : Program 8 15 (size command + 1) := compiled command 13 12

theorem program_runsIn (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ rf finalRank,
      RunsIn program (budget m.length rank.length arity.length (BinaryArithmetic.toNat rank) + 1)
        ((data r m rank arity [] [] out).withPC (some program.entry))
        ((data rf m finalRank arity [] []
          (stream m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out)).withPC none) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨n, hn, rf, last, he, hv, hl⟩ := command_eval r m rank arity out hm
  exact ⟨rf, last, ⟨n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 13 12⟩, hv, hl⟩

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
