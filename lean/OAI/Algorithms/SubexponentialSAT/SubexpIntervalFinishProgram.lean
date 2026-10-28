import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalCoreProgram
import OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms

namespace OAI.Algorithms

/-! Actual long division and scratch cleanup for the interval initializer. -/

namespace SubexponentialSAT.SubexpIntervalFinishProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def quotientPorts : Fin 8 → Fin 32 := ![10, 11, 12, 13, 14, 8, 15, 3]

theorem quotientPorts_injective : Function.Injective quotientPorts := by decide

def divisionState (r : Regs) (w : Words) (remainder numerator : List Bool) : Data :=
  ⟨r, Function.update (Function.update (state r w).stacks 15 numerator) 10 remainder⟩

@[simp] theorem divisionState_regs (r : Regs) (w : Words) (rem num : List Bool) :
    (divisionState r w rem num).regs = r := rfl

@[simp] theorem divisionState_ten (r : Regs) (w : Words) (rem num : List Bool) :
    (divisionState r w rem num).stacks 10 = rem := by simp [divisionState]

private theorem embed_quotient (frame r : Regs) (w : Words)
    (remainder numerator quotient : List Bool) :
    embedState id quotientPorts (state frame w)
      ⟨r, ModularQuotientPrograms.quotientStacks remainder (w 8) numerator quotient⟩ =
      divisionState r (Function.update w 3 quotient) remainder numerator := by
  apply embedState_eq_of_ports
  · exact Function.injective_id
  · exact quotientPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [divisionState, state, quotientPorts,
      ModularQuotientPrograms.quotientStacks]
  · intro i hi
    fin_cases i <;>
      first
      | exact (hi ⟨0, rfl⟩).elim
      | exact (hi ⟨1, rfl⟩).elim
      | exact (hi ⟨2, rfl⟩).elim
      | exact (hi ⟨3, rfl⟩).elim
      | exact (hi ⟨4, rfl⟩).elim
      | exact (hi ⟨5, rfl⟩).elim
      | exact (hi ⟨6, rfl⟩).elim
      | exact (hi ⟨7, rfl⟩).elim
      | simp [divisionState, state]

private theorem divisionState_start (r : Regs) (w : Words) (numerator : List Bool) :
    divisionState r w [] numerator =
      (⟨r, Function.update (state r w).stacks 15 numerator⟩ : Data) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [divisionState, state]

private theorem divisionState_clear (r : Regs) (w : Words) (remainder : List Bool) :
    (⟨readRegs r 0 1 none,
      Function.update (divisionState r w remainder []).stacks 10 []⟩ : Data) =
      state (readRegs r 0 1 none) w := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [divisionState, state]

abbrev divisionCmd : Cmd 8 32 :=
  .seq (ArithmeticExpressionSupport.copyCmd (port 9) 15 16)
    (.seq (.call (ProgramLinking.liftProgram
      ModularQuotientPrograms.quotientProgram id quotientPorts))
      (ArithmeticExpressionSupport.clearCmd 10))

theorem division_eval (r : Regs) (w : Words)
    (hd : 0 < BinaryArithmetic.toNat (w 8)) (ho : w 3 = []) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval divisionCmd t (state r w) (state rf (Function.update w 3 word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w 9) / BinaryArithmetic.toNat (w 8) ∧ word.length = (w 9).length ∧
      t ≤ 100 * ((w 8).length + (w 9).length + 1)^2 +
        9 * (w 9).length + 2 * (w 8).length + 8 := by
  have hc := ArithmeticExpressionSupport.copy_eval (port 9) 15 16 (state r w)
    (by decide) (by decide) (by decide)
    (state_work _ _ _ (by decide)) (state_work _ _ _ (by decide))
  let r1 := readRegs r 0 1 none
  have hc' : Eval (ArithmeticExpressionSupport.copyCmd (port 9) 15 16)
      (7 * (w 9).length + 5) (state r w) (divisionState r1 w [] (w 9)) := by
    simpa [state, state_port, divisionState_start, r1] using hc
  obtain ⟨rf, word, rem, hrun, hlen, hrlen, hval, _⟩ :=
    ModularQuotientPrograms.quotient_value r1 (w 8) (w 9) hd
  obtain ⟨t, ht, htrace⟩ := hrun
  have he := eval_call_lifted ModularQuotientPrograms.quotientProgram id quotientPorts
    (state r1 w) Function.injective_id quotientPorts_injective
    (a := ⟨r1, ModularQuotientPrograms.quotientStacks [] (w 8) (w 9) []⟩)
    (b := ⟨rf, ModularQuotientPrograms.quotientStacks rem (w 8) [] word⟩) htrace
  have hw : Function.update w 3 [] = w := by
    rw [← ho]
    exact Function.update_eq_self _ _
  simp only [embed_quotient, hw] at he
  have hclear := ArithmeticExpressionSupport.clear_eval (10 : Fin 32)
    (divisionState rf (Function.update w 3 word) rem [])
  have hclear' : Eval (ArithmeticExpressionSupport.clearCmd 10)
      (2 * rem.length + 3) (divisionState rf (Function.update w 3 word) rem [])
      (state (readRegs rf 0 1 none) (Function.update w 3 word)) := by
    simpa only [divisionState_regs, divisionState_clear, divisionState_ten] using hclear
  refine ⟨_, readRegs rf 0 1 none, word, hc'.seq (he.seq hclear'), hval, hlen, ?_⟩
  omega

def clearedWords : List (Fin 10) → Words → Words
  | [], w => w
  | i :: is, w => clearedWords is (Function.update w i [])

def clearWords : List (Fin 10) → Cmd 8 32
  | [] => .base .skip
  | i :: is => .seq (ArithmeticExpressionSupport.clearCmd (port i)) (clearWords is)

theorem clearedWords_bound (is : List (Fin 10)) (w : Words) (B : ℕ)
    (hB : ∀ i, (w i).length ≤ B) : ∀ i, (clearedWords is w i).length ≤ B := by
  induction is generalizing w with
  | nil => exact hB
  | cons j js ih =>
    apply ih (Function.update w j [])
    intro i
    by_cases h : i = j
    · subst i
      simpa only [Function.update_self, List.length_nil] using Nat.zero_le B
    · simpa [h] using hB i

theorem clearWords_eval (is : List (Fin 10)) (r : Regs) (w : Words) (B : ℕ)
    (hB : ∀ i, (w i).length ≤ B) :
    ∃ (t : ℕ) (rf : Regs), Eval (clearWords is) t (state r w)
      (state rf (clearedWords is w)) ∧ t ≤ is.length * (2 * B + 3) := by
  induction is generalizing r w with
  | nil => exact ⟨0, r, .base (.skip _), by simp⟩
  | cons i is ih =>
    have hc := ArithmeticExpressionSupport.clear_eval (port i) (state r w)
    have hc' : Eval (ArithmeticExpressionSupport.clearCmd (port i))
        (2 * (w i).length + 3) (state r w)
        (state (readRegs r 0 1 none) (Function.update w i [])) := by
      simpa only [state_port, state_update, state_regs] using hc
    have hB' : ∀ j, (Function.update w i [] j).length ≤ B := by
      intro j
      by_cases h : j = i
      · subst j
        simpa only [Function.update_self, List.length_nil] using Nat.zero_le B
      · simpa [h] using hB j
    obtain ⟨t, rf, he, ht⟩ := ih (readRegs r 0 1 none) (Function.update w i []) hB'
    refine ⟨_, rf, hc'.seq he, ?_⟩
    have := hB i
    simp only [List.length_cons]
    nlinarith

abbrev cleanup : Cmd 8 32 := clearWords [4, 5, 6, 7, 8, 9]

theorem cleanup_eval (regs : Regs) (w : Words) (r Q R word : List Bool)
    (h0 : w 0 = r) (h1 : w 1 = Q) (h2 : w 2 = R) (h3 : w 3 = word)
    (B : ℕ) (hB : ∀ i, (w i).length ≤ B) :
    ∃ (t : ℕ) (rf : Regs), Eval cleanup t (state regs w)
      (state rf (Function.update (inputWords r Q R) 3 word)) ∧
      t ≤ 6 * (2 * B + 3) := by
  obtain ⟨t, rf, he, ht⟩ := clearWords_eval [4, 5, 6, 7, 8, 9] regs w B hB
  have hw : clearedWords [4, 5, 6, 7, 8, 9] w =
      Function.update (inputWords r Q R) 3 word := by
    funext i
    fin_cases i <;> simp [clearedWords, inputWords, h0, h1, h2, h3]
  refine ⟨t, rf, ?_, ht⟩
  simpa only [cleanup, hw] using he

end SubexponentialSAT.SubexpIntervalFinishProgram

end OAI.Algorithms
