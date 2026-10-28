import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms

namespace OAI.Algorithms

/-!
# Actual field-parameter arithmetic on binary stack words

The fixed program receives `p` and `delta` on stacks 0 and 1. Stacks 0--7
are retained logical words, and stacks 8--15 are an initially empty work bank.
All width bounds concern actual words, including any leading zero padding.
-/

namespace SubexponentialSAT.SubexpFieldParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 8 → List Bool
abbrev Data := State 8 16

def port (i : Fin 8) : Fin 16 := ⟨i.val, by omega⟩

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 8 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 8) :
    (state r w).stacks (port i) = w i := by simp [state, port]

theorem state_work (r : Regs) (w : Words) (i : Fin 16) (hi : 8 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 8 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 8) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 8
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have := congrArg Fin.val he
      simp only [port] at this
      omega
    simp [state, Function.update_apply, hj, hji]

def inputWords (p delta : List Bool) : Words := ![p, delta, [], [], [], [], [], []]

def decrementPorts (i : Fin 8) : CounterForPrograms.Ports 8 16 where
  register := ⟨fun j => ⟨j.val, by omega⟩, by
    intro a b h
    exact Fin.ext (congrArg (fun j : Fin 8 => j.val) h)⟩
  counter := port i
  scratch := 13
  counter_ne_scratch := by
    intro h
    have := congrArg Fin.val h
    simp only [port] at this
    have := i.isLt
    omega

abbrev decrementCmd (i : Fin 8) : Cmd 8 16 :=
  CounterForPrograms.decrementCmd (decrementPorts i)

theorem decrement_eval (r : Regs) (w : Words) (i : Fin 8)
    (hp : 0 < BinaryArithmetic.toNat (w i)) :
    ∃ t rf word,
      Eval (decrementCmd i) t (state r w) (state rf (Function.update w i word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w i) - 1 ∧ word.length = (w i).length ∧
      t ≤ 8 * (w i).length + 8 := by
  let d := CounterForPrograms.decrementResult (decrementPorts i) (state r w)
  let word := CounterPrograms.ripple false (w i)
  have hs : (state r w).stacks (decrementPorts i).scratch = [] :=
    state_work r w 13 (by decide)
  have he := CounterForPrograms.decrement_eval (decrementPorts i) (state r w) hs
  have hd : d = state d.regs (Function.update w i word) := by
    rw [← state_update r d.regs w i word]
    apply CounterForPrograms.data_ext <;> try rfl
    funext j
    change d.stacks j = Function.update (state r w).stacks (port i) word j
    by_cases hj : j = port i
    · subst j
      rw [Function.update_self]
      change (CounterForPrograms.install (decrementPorts i) (state r w)
        false false _ _ []).stacks (decrementPorts i).counter = word
      rw [CounterForPrograms.install_counter]
      simp only [decrementPorts, state_port, word]
    · by_cases hjs : j = 13
      · subst j
        rw [Function.update_of_ne hj, state_work r w 13 (by decide)]
        change (CounterForPrograms.install (decrementPorts i) (state r w)
          false false _ _ []).stacks (decrementPorts i).scratch = []
        rw [CounterForPrograms.install_scratch]
      · rw [Function.update_of_ne hj]
        exact CounterForPrograms.install_other_stack (decrementPorts i) (state r w)
          false false _ _ [] j hj hjs
  have hv := CounterPrograms.value_decrement
    (bs := w i) (by simpa only [CounterPrograms.value_eq_toNat] using hp)
  have hl := CounterPrograms.decrement_length
    (bs := w i) (by simpa only [CounterPrograms.value_eq_toNat] using hp)
  refine ⟨CounterPrograms.rippleCost false (w i) + 1, d.regs, word, ?_, ?_, hl, ?_⟩
  · have hd' : CounterForPrograms.decrementResult (decrementPorts i) (state r w) =
        state d.regs (Function.update w i word) := hd
    rw [hd'] at he
    simpa only [decrementCmd, decrementPorts, state_port] using he
  · simp only [CounterPrograms.value_eq_toNat] at hv
    change BinaryArithmetic.toNat (CounterPrograms.ripple false (w i)) = _
    omega
  · have := CounterPrograms.rippleCost_le false (w i)
    omega

def arithmeticPorts (a b o : Fin 8) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 16 where
  left := port a
  right := port b
  out := port o
  work := ⟨fun j => ⟨8 + j.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩
  out_ne_left := by intro h; exact hoa (Fin.ext (congrArg (fun j : Fin 16 => j.val) h))
  out_ne_right := by intro h; exact hob (Fin.ext (congrArg (fun j : Fin 16 => j.val) h))
  work_ne_left := by
    intro i h
    have hval := congrArg (fun j : Fin 16 => j.val) h
    change 8 + i.val = a.val at hval
    omega
  work_ne_right := by
    intro i h
    have hval := congrArg (fun j : Fin 16 => j.val) h
    change 8 + i.val = b.val at hval
    omega
  work_ne_out := by
    intro i h
    have hval := congrArg (fun j : Fin 16 => j.val) h
    change 8 + i.val = o.val at hval
    omega

abbrev multiplyCmd (a b o : Fin 8) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 16 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 8)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      exact state_work r w _ (by change 8 ≤ 8 + i.val; omega)
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

abbrev coreCommand (k : ℕ) : Cmd 8 16 :=
  .seq (ArithmeticExpressionSupport.pushWord (port 2) (8 * k).bits)
    (.seq (multiplyCmd 0 0 3 (by decide) (by decide))
      (.seq (multiplyCmd 3 3 4 (by decide) (by decide))
        (.seq (decrementCmd 4)
          (.seq (multiplyCmd 2 1 5 (by decide) (by decide))
            (multiplyCmd 5 0 6 (by decide) (by decide))))))

/-- Explicit width parameter for arbitrary, possibly padded input words. -/
def width (k : ℕ) (p delta : List Bool) : ℕ :=
  p.length + delta.length + (8 * k).bits.length + 1

theorem width_pos (k : ℕ) (p delta : List Bool) : 0 < width k p delta := by
  unfold width
  omega

/-- Four genuine multiplication calls and one decrement compute the field
size and denominator, preserving the actual input words. -/
theorem core_eval (k : ℕ) (r : Regs) (p delta : List Bool) (hp : 0 < BinaryArithmetic.toNat p) :
    ∃ t rf w,
      Eval (coreCommand k) t (state r (inputWords p delta)) (state rf w) ∧
      w 0 = p ∧ w 1 = delta ∧
      BinaryArithmetic.toNat (w 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
      BinaryArithmetic.toNat (w 6) = 8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p ∧ w 7 = [] ∧
      (∀ j, (w j).length ≤ 4 * width k p delta) ∧
      t ≤ 10000 * (width k p delta) ^ 2 := by
  let c := (8 * k).bits
  let w0 := inputWords p delta
  let w1 := Function.update w0 2 c
  obtain ⟨r1, hc⟩ := ArithmeticExpressionSupport.pushWord_eval (port 2) c (state r w0)
  have hc' : Eval (ArithmeticExpressionSupport.pushWord (port 2) c)
      (2 * c.length) (state r w0) (state r1 w1) := by
    simpa only [state_port, show w0 2 = [] from rfl,
      List.append_nil, state_update] using hc
  obtain ⟨t1, r2, p2, h1, hv1, hl1, ht1⟩ :=
    multiply_eval r1 w1 0 0 3 (by decide) (by decide) (by simp [w1, w0, inputWords])
  let w2 := Function.update w1 3 p2
  obtain ⟨t2, r3, p4, h2, hv2, hl2, ht2⟩ :=
    multiply_eval r2 w2 3 3 4 (by decide) (by decide) (by simp [w2, w1, w0, inputWords])
  simp [w2, w1, w0, inputWords] at hv1 hl1 ht1 hv2 hl2 ht2
  have hp4 : BinaryArithmetic.toNat p4 = BinaryArithmetic.toNat p ^ 4 := by rw [hv2, hv1]; ring
  let w3 := Function.update w2 4 p4
  obtain ⟨tp, r4, q, hpred, hvp, hlp, htp⟩ := decrement_eval r3 w3 4 (by
    simpa only [w3, Function.update_self, hp4] using pow_pos hp 4)
  simp only [w3, Function.update_self] at hvp hlp htp
  let w4 := Function.update w3 4 q
  obtain ⟨t3, r5, dc, h3, hv3, hl3, ht3⟩ :=
    multiply_eval r4 w4 2 1 5 (by decide) (by decide) (by
      simp [w4, w3, w2, w1, w0, inputWords])
  let w5 := Function.update w4 5 dc
  obtain ⟨t4, r6, den, h4, hv4, hl4, ht4⟩ :=
    multiply_eval r5 w5 5 0 6 (by decide) (by decide) (by
      simp [w5, w4, w3, w2, w1, w0, inputWords])
  simp [w5, w4, w3, w2, w1, w0, inputWords] at hv3 hl3 ht3 hv4 hl4 ht4
  let w6 := Function.update w5 6 den
  let t := 2 * c.length + (t1 + (t2 + (tp + (t3 + t4))))
  have he : Eval (coreCommand k) t (state r (inputWords p delta)) (state r6 w6) :=
    hc'.seq (h1.seq (h2.seq (hpred.seq (h3.seq h4))))
  refine ⟨t, r6, w6, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simpa [w6, w5, w4, hp4] using hvp
  · simp only [w6, Function.update_self, hv4, hv3]
    rw [show BinaryArithmetic.toNat c = 8 * k from ArithmeticExpressionSupport.bits_value _]
    ring
  · simp [w6, w5, w4, w3, w2, w1, w0, inputWords]
  · intro j
    fin_cases j <;> simp [w6, w5, w4, w3, w2, w1, w0, inputWords]
    all_goals dsimp [width, c] at *; omega
  · let W := width k p delta
    have hW : 1 ≤ W := width_pos k p delta
    have hWsq : W ≤ W ^ 2 := by nlinarith
    have hmul (a t' : ℕ) (ha : a ≤ 4 * W) (ht : t' ≤ 100 * a ^ 2) :
        t' ≤ 1600 * W ^ 2 := by
      calc
        t' ≤ 100 * a ^ 2 := ht
        _ ≤ 100 * (4 * W) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha _)
        _ = _ := by ring
    have hb1 : t1 ≤ 1600 * W ^ 2 := hmul _ _ (by dsimp [W, width, c]; omega) ht1
    have hb2 : t2 ≤ 1600 * W ^ 2 := hmul _ _ (by dsimp [W, width, c] at *; omega) ht2
    have hb3 : t3 ≤ 1600 * W ^ 2 := hmul _ _ (by dsimp [W, width, c]; omega) ht3
    have hb4 : t4 ≤ 1600 * W ^ 2 := hmul _ _ (by dsimp [W, width, c] at *; omega) ht4
    have hbp : tp ≤ 32 * W := by dsimp [W, width, c] at *; omega
    have hbc : c.length ≤ W := by dsimp [W, width, c]; omega
    change t ≤ 10000 * W ^ 2
    dsimp [t]
    omega

def quotientPorts : Fin 8 → Fin 16 := ![8, 9, 10, 11, 12, 6, 13, 7]

theorem quotientPorts_injective : Function.Injective quotientPorts := by decide

def divisionState (r : Regs) (w : Words) (remainder numerator : List Bool) : Data :=
  ⟨r, Function.update (Function.update (state r w).stacks 13 numerator) 8 remainder⟩

@[simp] theorem divisionState_regs (r : Regs) (w : Words) (rem num : List Bool) :
    (divisionState r w rem num).regs = r := rfl

@[simp] theorem divisionState_eight (r : Regs) (w : Words) (rem num : List Bool) :
    (divisionState r w rem num).stacks 8 = rem := by simp [divisionState]

private theorem embed_quotient (frame r : Regs) (w : Words)
    (remainder numerator quotient : List Bool) :
    embedState id quotientPorts (state frame w)
      ⟨r, ModularQuotientPrograms.quotientStacks remainder (w 6) numerator quotient⟩ =
      divisionState r (Function.update w 7 quotient) remainder numerator := by
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
      (⟨r, Function.update (state r w).stacks 13 numerator⟩ : Data) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [divisionState, state]

private theorem divisionState_clear (r : Regs) (w : Words) (remainder : List Bool) :
    (⟨readRegs r 0 1 none,
      Function.update (divisionState r w remainder []).stacks 8 []⟩ : Data) =
      state (readRegs r 0 1 none) w := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [divisionState, state]

abbrev divisionCmd : Cmd 8 16 :=
  .seq (ArithmeticExpressionSupport.copyCmd (port 4) 13 14)
    (.seq (.call (ProgramLinking.liftProgram
      ModularQuotientPrograms.quotientProgram id quotientPorts))
      (ArithmeticExpressionSupport.clearCmd 8))

/-- Divide a copied numerator by the stored denominator. Both source words
survive unchanged and the temporary remainder is actually cleared. -/
theorem division_eval (r : Regs) (w : Words)
    (hd : 0 < BinaryArithmetic.toNat (w 6)) (ho : w 7 = []) :
    ∃ t rf word,
      Eval divisionCmd t (state r w) (state rf (Function.update w 7 word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w 4) / BinaryArithmetic.toNat (w 6) ∧ word.length = (w 4).length ∧
      t ≤ 100 * ((w 6).length + (w 4).length + 1) ^ 2 +
        9 * (w 4).length + 2 * (w 6).length + 8 := by
  have hc := ArithmeticExpressionSupport.copy_eval (port 4) 13 14 (state r w)
    (by decide) (by decide) (by decide)
    (state_work r w 13 (by decide)) (state_work r w 14 (by decide))
  let r1 := readRegs r 0 1 none
  have hc' : Eval (ArithmeticExpressionSupport.copyCmd (port 4) 13 14)
      (7 * (w 4).length + 5) (state r w) (divisionState r1 w [] (w 4)) := by
    simpa [state, port, state_port, divisionState_start, r1] using hc
  obtain ⟨rf, word, rem, hrun, hlen, hrlen, hval, _⟩ :=
    ModularQuotientPrograms.quotient_value r1 (w 6) (w 4) hd
  obtain ⟨t, ht, htrace⟩ := hrun
  have he := eval_call_lifted ModularQuotientPrograms.quotientProgram id quotientPorts
    (state r1 w) Function.injective_id quotientPorts_injective
    (a := ⟨r1, ModularQuotientPrograms.quotientStacks [] (w 6) (w 4) []⟩)
    (b := ⟨rf, ModularQuotientPrograms.quotientStacks rem (w 6) [] word⟩) htrace
  have hw : Function.update w 7 [] = w := by
    rw [← ho]
    exact Function.update_eq_self _ _
  simp only [embed_quotient, hw] at he
  have hclear := ArithmeticExpressionSupport.clear_eval (8 : Fin 16)
    (divisionState rf (Function.update w 7 word) rem [])
  have hclear' : Eval (ArithmeticExpressionSupport.clearCmd 8)
      (2 * rem.length + 3) (divisionState rf (Function.update w 7 word) rem [])
      (state (readRegs rf 0 1 none) (Function.update w 7 word)) := by
    simpa only [divisionState_regs, divisionState_clear, divisionState_eight] using hclear
  refine ⟨(7 * (w 4).length + 5) + (t + (2 * rem.length + 3)),
    readRegs rf 0 1 none, word, hc'.seq (he.seq hclear'), hval, hlen, ?_⟩
  omega

abbrev command (k : ℕ) : Cmd 8 16 := .seq (coreCommand k) divisionCmd

/-- The instruction table depends only on the fixed parameter `k`. -/
def program (k : ℕ) := compiled (command k) (0 : Fin 16) 7

theorem command_eval (k : ℕ) (hk : 0 < k) (r : Regs) (p delta : List Bool)
    (hp : 0 < BinaryArithmetic.toNat p) (hd : 0 < BinaryArithmetic.toNat delta) :
    ∃ (t : ℕ) (d : Data),
      Eval (command k) t (state r (inputWords p delta)) d ∧
      d.stacks 0 = p ∧ d.stacks 1 = delta ∧
      BinaryArithmetic.toNat (d.stacks 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
      BinaryArithmetic.toNat (d.stacks 6) = 8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p ∧
      BinaryArithmetic.toNat (d.stacks 7) = (BinaryArithmetic.toNat p ^ 4 - 1) / (8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p) ∧
      (∀ j, (d.stacks j).length ≤ 4 * width k p delta) ∧
      (∀ j, 8 ≤ j.val → d.stacks j = []) ∧
      t ≤ 20000 * (width k p delta) ^ 2 := by
  obtain ⟨t1, r1, w, hcore, hw0, hw1, hw4, hw6, hw7, hwidth, ht1⟩ :=
    core_eval k r p delta hp
  obtain ⟨t2, rf, word, hdiv, hv, hl, ht2⟩ := division_eval r1 w (by
    rw [hw6]
    positivity) hw7
  refine ⟨t1 + t2, state rf (Function.update w 7 word), hcore.seq hdiv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [state, hw0]
  · simp [state, hw1]
  · simpa [state] using hw4
  · simpa [state] using hw6
  · simpa [state, hw4, hw6] using hv
  · intro j
    by_cases hj : j.val < 8
    · change (if h : j.val < 8 then Function.update w 7 word ⟨j.val, h⟩ else []).length ≤ _
      rw [dite_eq_left hj]
      by_cases h7 : (⟨j.val, hj⟩ : Fin 8) = 7
      · rw [h7, Function.update_self, hl]
        exact hwidth 4
      · rw [Function.update_of_ne h7]
        exact hwidth _
    · rw [state_work _ _ _ (by omega)]
      simp
  · exact state_work _ _
  · let W := width k p delta
    have hW : 1 ≤ W := width_pos k p delta
    have hWsq : W ≤ W ^ 2 := by nlinarith
    have h4 := hwidth 4
    have h6 := hwidth 6
    have hs : (w 6).length + (w 4).length + 1 ≤ 9 * W := by omega
    have hpw : 100 * ((w 6).length + (w 4).length + 1) ^ 2 ≤ 8100 * W ^ 2 := by
      calc
        _ ≤ 100 * (9 * W) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)
        _ = _ := by ring
    change t1 + t2 ≤ 20000 * W ^ 2
    change t1 ≤ 10000 * W ^ 2 at ht1
    omega

/-- Actual halted execution, exact field-parameter values, retained-word
width bound, and empty scratch bank. -/
theorem run_value (k : ℕ) (hk : 0 < k) (r : Regs) (p delta : List Bool)
    (hp : 0 < BinaryArithmetic.toNat p) (hd : 0 < BinaryArithmetic.toNat delta) :
    ∃ d : Data,
      d.stacks 0 = p ∧ d.stacks 1 = delta ∧
      BinaryArithmetic.toNat (d.stacks 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
      BinaryArithmetic.toNat (d.stacks 6) = 8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p ∧
      BinaryArithmetic.toNat (d.stacks 7) = (BinaryArithmetic.toNat p ^ 4 - 1) / (8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p) ∧
      (∀ j, (d.stacks j).length ≤ 4 * width k p delta) ∧
      (∀ j, 8 ≤ j.val → d.stacks j = []) ∧
      BitProgram.RunsIn (program k) (30000 * (width k p delta) ^ 2)
        ((state r (inputWords p delta)).withPC (some (program k).entry)) (d.withPC none) := by
  obtain ⟨t, d, he, hp0, hd1, hq, hden, hR, hlen, hwork, ht⟩ :=
    command_eval k hk r p delta hp hd
  refine ⟨d, hp0, hd1, hq, hden, hR, hlen, hwork, t + 1, ?_,
    compiled_halt_trace he 0 7⟩
  have hW := width_pos k p delta
  have hWs : 1 ≤ (width k p delta) ^ 2 := by nlinarith
  omega

/-- Compilation to primitive tapes changes the bound by a constant depending
only on the fixed instruction table. -/
theorem primitive_value (k : ℕ) (hk : 0 < k) (r : Regs) (p delta : List Bool)
    (hp : 0 < BinaryArithmetic.toNat p) (hd : 0 < BinaryArithmetic.toNat delta) :
    ∃ d : Data,
      BinaryArithmetic.toNat (d.stacks 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
      BinaryArithmetic.toNat (d.stacks 7) = (BinaryArithmetic.toNat p ^ 4 - 1) / (8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p) ∧
      (∀ j, (d.stacks j).length ≤ 4 * width k p delta) ∧
      Computation.RunsIn (BitProgram.primitive (program k)).step
        (BitProgram.primitiveOverhead (program k) * (30000 * (width k p delta) ^ 2))
        (BitProgram.primitiveCfg (program k)
          ((state r (inputWords p delta)).withPC (some (program k).entry)))
        (BitProgram.primitiveCfg (program k) (d.withPC none)) := by
  obtain ⟨d, _, _, hq, _, hR, hlen, _, hr⟩ := run_value k hk r p delta hp hd
  exact ⟨d, hq, hR, hlen, BitProgram.primitive_execution (program k) hr⟩

/-- Bounds supplied by actual word producers yield a uniform polynomial
execution bound. In particular, the proof does not infer widths from values. -/
theorem run_polynomial (k : ℕ) (hk : 0 < k) (r : Regs) (p delta : List Bool)
    (hp : 0 < BinaryArithmetic.toNat p) (hd : 0 < BinaryArithmetic.toNat delta) (n C e : ℕ)
    (hlp : p.length ≤ C * (n + 1) ^ e) (hld : delta.length ≤ C * (n + 1) ^ e) :
    ∃ d : Data,
      d.stacks 0 = p ∧ d.stacks 1 = delta ∧
      BinaryArithmetic.toNat (d.stacks 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
      BinaryArithmetic.toNat (d.stacks 7) = (BinaryArithmetic.toNat p ^ 4 - 1) / (8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p) ∧
      (∀ j, (d.stacks j).length ≤
        4 * (2 * C + (8 * k).bits.length + 1) * (n + 1) ^ e) ∧
      BitProgram.RunsIn (program k)
        (30000 * (2 * C + (8 * k).bits.length + 1) ^ 2 * (n + 1) ^ (e * 2))
        ((state r (inputWords p delta)).withPC (some (program k).entry)) (d.withPC none) := by
  obtain ⟨d, hp0, hd1, hq, _, hR, hlen, _, hr⟩ := run_value k hk r p delta hp hd
  have hne : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hw : width k p delta ≤ (2 * C + (8 * k).bits.length + 1) * (n + 1) ^ e := by
    dsimp [width]
    nlinarith
  refine ⟨d, hp0, hd1, hq, hR, ?_, hr.mono ?_⟩
  · intro j
    calc
      _ ≤ 4 * width k p delta := hlen j
      _ ≤ 4 * ((2 * C + (8 * k).bits.length + 1) * (n + 1) ^ e) :=
        Nat.mul_le_mul_left _ hw
      _ = _ := by ring
  · calc
      _ ≤ 30000 * ((2 * C + (8 * k).bits.length + 1) * (n + 1) ^ e) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw _)
      _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Concrete local endpoint contract, convenient for callers that lift this
stage into a larger persistent state. -/
def Output (k : ℕ) (p delta : List Bool) (d : Data) : Prop :=
  d.stacks 0 = p ∧ d.stacks 1 = delta ∧
  BinaryArithmetic.toNat (d.stacks 4) = BinaryArithmetic.toNat p ^ 4 - 1 ∧
  BinaryArithmetic.toNat (d.stacks 6) = 8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p ∧
  BinaryArithmetic.toNat (d.stacks 7) = (BinaryArithmetic.toNat p ^ 4 - 1) / (8 * BinaryArithmetic.toNat delta * k * BinaryArithmetic.toNat p) ∧
  (∀ j, (d.stacks j).length ≤ 4 * width k p delta) ∧
  (∀ j, 8 ≤ j.val → d.stacks j = [])

theorem lifted_output {R S : ℕ} (k : ℕ) (hk : 0 < k) (r : Regs)
    (p delta : List Bool) (hp : 0 < BinaryArithmetic.toNat p) (hd : 0 < BinaryArithmetic.toNat delta)
    (register : Fin 8 → Fin R) (stack : Fin 16 → Fin S)
    (frame : State R S) (hr : Function.Injective register)
    (hs : Function.Injective stack) :
    ∃ t d, t ≤ 30000 * (width k p delta) ^ 2 ∧ Output k p delta d ∧
      Eval (.call (ProgramLinking.liftProgram (program k) register stack)) t
        (embedState register stack frame (state r (inputWords p delta)))
        (embedState register stack frame d) := by
  obtain ⟨d, hp0, hd1, hq, hden, hR, hlen, hwork, t, ht, htrace⟩ :=
    run_value k hk r p delta hp hd
  exact ⟨t, d, ht, ⟨hp0, hd1, hq, hden, hR, hlen, hwork⟩,
    eval_call_lifted (program k) register stack frame hr hs
      (a := state r (inputWords p delta)) (b := d) htrace⟩

end SubexponentialSAT.SubexpFieldParameterProgram

end OAI.Algorithms
