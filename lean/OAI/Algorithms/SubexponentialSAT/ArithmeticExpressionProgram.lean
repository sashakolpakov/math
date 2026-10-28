import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionBounds
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.CounterPredProgram

namespace OAI.Algorithms

/-! Fixed arithmetic expressions, compiled below to actual finite bit programs.
The only varying semantic input is the natural number represented by the input word. -/

namespace SubexponentialSAT.ArithmeticExpressionProgram

inductive Expr where
  | input
  | const (value : ℕ)
  | add (left right : Expr)
  | mul (left right : Expr)
  | pred (arg : Expr)
  deriving DecidableEq

def eval (M : ℕ) : Expr → ℕ
  | .input => M
  | .const n => n
  | .add a b => eval M a + eval M b
  | .mul a b => eval M a * eval M b
  | .pred a => eval M a - 1

/-- All work allocation is determined by the fixed expression tree. -/
def slots : Expr → ℕ
  | .input | .const _ => 16
  | .add a b | .mul a b => 16 + slots a + slots b
  | .pred a => 16 + slots a

theorem slots_ge (e : Expr) : 16 ≤ slots e := by
  cases e <;> simp [slots] <;> omega

def widthCoeff : Expr → ℕ
  | .input => 1
  | .const n => n.bits.length
  | .add a b | .mul a b => widthCoeff a + widthCoeff b + 1
  | .pred a => widthCoeff a

def timeCoeff : Expr → ℕ
  | .input => 20
  | .const n => 2 * n.bits.length
  | .add a b | .mul a b => timeCoeff a + timeCoeff b +
      100 * (widthCoeff a + widthCoeff b + 1)^2 + 100 * (widthCoeff a + widthCoeff b + 1)
  | .pred a => timeCoeff a + 100 * (widthCoeff a + 1)

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def inputPort {S : ℕ} (h : 2 ≤ S) : Fin S := ⟨0, by omega⟩
def outputPort {S : ℕ} (h : 2 ≤ S) : Fin S := ⟨1, by omega⟩

theorem input_ne_output {S : ℕ} (h : 2 ≤ S) : inputPort h ≠ outputPort h := by
  intro he
  have := congrArg Fin.val he
  simp [inputPort, outputPort] at this

def state {S : ℕ} (h : 2 ≤ S) (regs : Fin 8 → Bool) (input output : List Bool) : State 8 S :=
  ⟨regs, Function.update (Function.update (fun _ => []) (inputPort h) input)
    (outputPort h) output⟩

@[simp] theorem state_input {S : ℕ} (h : 2 ≤ S) (regs : Fin 8 → Bool)
    (input output : List Bool) : (state h regs input output).stacks (inputPort h) = input := by
  simp [state, input_ne_output]

@[simp] theorem state_output {S : ℕ} (h : 2 ≤ S) (regs : Fin 8 → Bool)
    (input output : List Bool) : (state h regs input output).stacks (outputPort h) = output := by
  simp [state]

theorem state_other {S : ℕ} (h : 2 ≤ S) (regs : Fin 8 → Bool)
    (input output : List Bool) (i : Fin S) (hi : i ≠ inputPort h) (ho : i ≠ outputPort h) :
    (state h regs input output).stacks i = [] := by
  simp [state, hi, ho]

def leftBlock (a b : ℕ) : Fin a ↪ Fin (16 + a + b) where
  toFun i := ⟨16 + i.val, by omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    simp only at this
    omega

def rightBlock (a b : ℕ) : Fin b ↪ Fin (16 + a + b) where
  toFun i := ⟨16 + a + i.val, by omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    simp only at this
    omega

def lowPort (a b : ℕ) (i : Fin 16) : Fin (16 + a + b) := ⟨i.val, by omega⟩

theorem left_ne_right (a b : ℕ) (i : Fin a) (j : Fin b) :
    leftBlock a b i ≠ rightBlock a b j := by
  intro he
  have := congrArg Fin.val he
  change 16 + i.val = 16 + a + j.val at this
  omega

theorem left_ne_low (a b : ℕ) (i : Fin a) (j : Fin 16) :
    leftBlock a b i ≠ lowPort a b j := by
  intro he
  have := congrArg Fin.val he
  change 16 + i.val = j.val at this
  have := j.isLt
  omega

theorem right_ne_low (a b : ℕ) (i : Fin b) (j : Fin 16) :
    rightBlock a b i ≠ lowPort a b j := by
  intro he
  have := congrArg Fin.val he
  change 16 + a + i.val = j.val at this
  have := j.isLt
  omega


open SubexponentialSAT.ArithmeticExpressionSupport

def workBlock (a b : ℕ) : Fin 5 ↪ Fin (16 + a + b) where
  toFun i := lowPort a b ⟨i.val + 2, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [lowPort] at this
    omega

def binaryPorts (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : ArithmeticCalls.Ports (16 + a + b) where
  left := leftBlock a b (outputPort ha)
  right := rightBlock a b (outputPort hb)
  out := lowPort a b 1
  work := workBlock a b
  out_ne_left := (left_ne_low a b (outputPort ha) 1).symm
  out_ne_right := (right_ne_low a b (outputPort hb) 1).symm
  work_ne_left := fun i => (left_ne_low a b (outputPort ha) _).symm
  work_ne_right := fun i => (right_ne_low a b (outputPort hb) _).symm
  work_ne_out := by
    intro i h
    have := congrArg Fin.val h
    change i.val + 2 = 1 at this
    omega

abbrev blockCall {a S : ℕ} (c : Cmd 8 a) (h : 2 ≤ a) (block : Fin a ↪ Fin S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram (compiled c (inputPort h) (outputPort h)) id block)

abbrev binaryCmd {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (isMul : Bool) (ca : Cmd 8 a) (cb : Cmd 8 b) : Cmd 8 (16 + a + b) :=
  .seq (copyCmd (lowPort a b 0) (leftBlock a b (inputPort ha)) (lowPort a b 7))
  (.seq (blockCall ca ha (leftBlock a b))
  (.seq (copyCmd (lowPort a b 0) (rightBlock a b (inputPort hb)) (lowPort a b 7))
  (.seq (blockCall cb hb (rightBlock a b))
  (.seq (if isMul then ArithmeticCalls.multiplyAt (binaryPorts a b ha hb)
          else ArithmeticCalls.addAt (binaryPorts a b ha hb))
  (.seq (clearCmd (rightBlock a b (outputPort hb)))
  (.seq (clearCmd (rightBlock a b (inputPort hb)))
  (.seq (clearCmd (leftBlock a b (outputPort ha)))
        (clearCmd (leftBlock a b (inputPort ha))))))))))

def predPorts (a : ℕ) : CounterForPrograms.Ports 8 (16 + a) where
  register := ⟨Fin.castAdd 5, by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 8 => x.val) h⟩
  counter := lowPort a 0 1
  scratch := lowPort a 0 2
  counter_ne_scratch := by
    intro h
    have := congrArg Fin.val h
    change (1 : ℕ) = 2 at this
    omega

abbrev unaryCmd {a : ℕ} (ha : 2 ≤ a) (ca : Cmd 8 a) : Cmd 8 (16 + a) :=
  .seq (copyCmd (lowPort a 0 0) (leftBlock a 0 (inputPort ha)) (lowPort a 0 7))
  (.seq (blockCall ca ha (leftBlock a 0))
  (.seq (copyCmd (leftBlock a 0 (outputPort ha)) (lowPort a 0 1) (lowPort a 0 7))
  (.seq (CounterPredProgram.predCmd (predPorts a))
  (.seq (clearCmd (leftBlock a 0 (outputPort ha)))
        (clearCmd (leftBlock a 0 (inputPort ha)))))))

/-- Compiling a call depends only on the fixed child syntax and port layout. -/
def command : (e : Expr) → Cmd 8 (slots e)
  | .input => copyCmd (S := 16) 0 1 2
  | .const n => pushWord (1 : Fin 16) n.bits
  | .add a b => binaryCmd (by have := slots_ge a; omega) (by have := slots_ge b; omega)
      false (command a) (command b)
  | .mul a b => binaryCmd (by have := slots_ge a; omega) (by have := slots_ge b; omega)
      true (command a) (command b)
  | .pred a => unaryCmd (by have := slots_ge a; omega) (command a)

abbrev Spec (e : Expr) {S : ℕ} (h : 2 ≤ S) (c : Cmd 8 S) : Prop :=
  ∀ (xs : List Bool) (regs : Fin 8 → Bool), ∃ n word rf,
    Eval c n (state h regs xs []) (state h rf xs word) ∧
    BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
    word.length ≤ widthCoeff e * (xs.length + 1) ∧
    n ≤ timeCoeff e * (xs.length + 1)^2

theorem block_eval {e : Expr} {a S : ℕ} {h : 2 ≤ a} {c : Cmd 8 a}
    (hc : Spec e h c) (block : Fin a ↪ Fin S) (d : State 8 S) (xs : List Bool)
    (clean : d.stacks ∘ block = (state h d.regs xs []).stacks) :
    ∃ n word rf,
      Eval (blockCall c h block) (n + 1) d
        ⟨rf, Function.update d.stacks (block (outputPort h)) word⟩ ∧
      BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
      word.length ≤ widthCoeff e * (xs.length + 1) ∧
      n ≤ timeCoeff e * (xs.length + 1)^2 := by
  obtain ⟨n, word, rf, hr, hv, hw, ht⟩ := hc xs d.regs
  refine ⟨n, word, rf, ?_, hv, hw, ht⟩
  apply call_on_block c (inputPort h) (outputPort h) block d
    (state h d.regs xs []) (state h rf xs word) word hr rfl clean.symm
  simp [state]

attribute [simp] input_ne_output left_ne_low right_ne_low left_ne_right

@[simp] theorem output_ne_input {S : ℕ} (h : 2 ≤ S) : outputPort h ≠ inputPort h :=
  (input_ne_output h).symm

@[simp] theorem low_ne_left (a b : ℕ) (i : Fin 16) (j : Fin a) :
    lowPort a b i ≠ leftBlock a b j := (left_ne_low a b j i).symm
@[simp] theorem low_ne_right (a b : ℕ) (i : Fin 16) (j : Fin b) :
    lowPort a b i ≠ rightBlock a b j := (right_ne_low a b j i).symm
@[simp] theorem right_ne_left (a b : ℕ) (i : Fin b) (j : Fin a) :
    rightBlock a b i ≠ leftBlock a b j := (left_ne_right a b j i).symm

@[simp] theorem lowPort_eq {a b : ℕ} {i j : Fin 16} :
    lowPort a b i = lowPort a b j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun x : Fin (16 + a + b) => x.val) h
  · rintro rfl
    rfl

theorem initial_stacks {S : ℕ} (h : 2 ≤ S) (r : Fin 8 → Bool) (xs : List Bool) :
    (state h r xs []).stacks = Function.update (fun _ => []) (inputPort h) xs := by
  funext i
  by_cases hi : i = inputPort h
  · subst i
    simp [state]
  · simp [state, Function.update_apply, hi]

theorem parent_input (a b : ℕ) (h : 2 ≤ 16 + a + b) : inputPort h = lowPort a b 0 := rfl
theorem parent_output (a b : ℕ) (h : 2 ≤ 16 + a + b) : outputPort h = lowPort a b 1 := rfl

@[simp] theorem left_ne_parent_input (a b : ℕ) (h : 2 ≤ 16 + a + b) (i : Fin a) :
    leftBlock a b i ≠ inputPort h := left_ne_low a b i 0

@[simp] theorem left_ne_parent_output (a b : ℕ) (h : 2 ≤ 16 + a + b) (i : Fin a) :
    leftBlock a b i ≠ outputPort h := left_ne_low a b i 1

@[simp] theorem right_ne_parent_input (a b : ℕ) (h : 2 ≤ 16 + a + b) (i : Fin b) :
    rightBlock a b i ≠ inputPort h := right_ne_low a b i 0

@[simp] theorem right_ne_parent_output (a b : ℕ) (h : 2 ≤ 16 + a + b) (i : Fin b) :
    rightBlock a b i ≠ outputPort h := right_ne_low a b i 1

@[simp] theorem work_ne_parent_input (a b : ℕ) (h : 2 ≤ 16 + a + b) (i : Fin 5) :
    workBlock a b i ≠ inputPort h := by
  intro he
  have hv := congrArg Fin.val he
  change i.val + 2 = 0 at hv
  omega

@[simp] theorem work_ne_parent_output (a b : ℕ) (h : 2 ≤ 16 + a + b) (i : Fin 5) :
    workBlock a b i ≠ outputPort h := by
  intro he
  have hv := congrArg Fin.val he
  change i.val + 2 = 1 at hv
  omega

theorem input_spec : Spec .input (by decide : 2 ≤ 16) (copyCmd 0 1 2) := by
  intro xs regs
  have hr := copy_eval (0 : Fin 16) 1 2 (state (by decide) regs xs [])
    (by decide) (by decide) (by decide)
    (by simp [state, inputPort, outputPort]) (by simp [state, inputPort, outputPort])
  refine ⟨7 * xs.length + 5, xs, readRegs regs 0 1 none, ?_, rfl, ?_, ?_⟩
  · simpa [state, inputPort, outputPort] using hr
  · simp [widthCoeff]
  · simp only [timeCoeff]
    nlinarith

theorem const_spec (n : ℕ) : Spec (.const n) (by decide : 2 ≤ 16) (pushWord 1 n.bits) := by
  intro xs regs
  obtain ⟨rf, hr⟩ := pushWord_eval (1 : Fin 16) n.bits (state (by decide) regs xs [])
  refine ⟨2 * n.bits.length, n.bits, rf, ?_, bits_value n, ?_, ?_⟩
  · simpa [state, inputPort, outputPort] using hr
  · simp only [widthCoeff]
    nlinarith
  · simp only [timeCoeff]
    have h : 1 ≤ (xs.length + 1)^2 := by
      have hp : 0 < (xs.length + 1)^2 := pow_pos (by omega) _
      omega
    simpa using Nat.mul_le_mul_left (2 * n.bits.length) h


theorem binary_spec {ea eb : Expr} {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (isMul : Bool) (ca : Cmd 8 a) (cb : Cmd 8 b)
    (hca : Spec ea ha ca) (hcb : Spec eb hb cb) :
    Spec (if isMul then .mul ea eb else .add ea eb) (by omega)
      (binaryCmd ha hb isMul ca cb) := by
  intro xs regs
  let hp : 2 ≤ 16 + a + b := by omega
  let d0 := state hp regs xs []
  let d1 : State 8 (16 + a + b) :=
    ⟨readRegs d0.regs 0 1 none, Function.update d0.stacks (leftBlock a b (inputPort ha)) xs⟩
  have hleft0 (i : Fin a) : leftBlock a b i ≠ (0 : Fin (16 + a + b)) :=
    left_ne_low a b i 0
  have hright0 (i : Fin b) : rightBlock a b i ≠ (0 : Fin (16 + a + b)) :=
    right_ne_low a b i 0
  have htmp0 : lowPort a b 7 ≠ (0 : Fin (16 + a + b)) := by
    intro h
    have := congrArg Fin.val h
    simp [lowPort] at this
  have hd0source : d0.stacks (lowPort a b 0) = xs := by
    simpa only [d0, ← parent_input a b hp] using state_input hp regs xs []
  have hcopyA : Eval
      (copyCmd (lowPort a b 0) (leftBlock a b (inputPort ha)) (lowPort a b 7))
      (7 * xs.length + 5) d0 d1 := by
    have h :=
      copy_eval (lowPort a b 0) (leftBlock a b (inputPort ha)) (lowPort a b 7) d0
        (by simp) (by simp) (by simp)
        (by simp [d0, initial_stacks ])
        (by simp [d0, initial_stacks, inputPort, htmp0])
    rw [hd0source] at h
    simpa only [d1] using h
  have hcleanA : d1.stacks ∘ leftBlock a b = (state ha d1.regs xs []).stacks := by
    funext i
    simp [d1, d0, initial_stacks, Function.comp_apply, Function.update_apply,
      (leftBlock a b).injective.eq_iff ]
  obtain ⟨na, wa, ra, heA, hvA, hwA, htA⟩ := block_eval hca (leftBlock a b) d1 xs hcleanA
  let d2 : State 8 (16 + a + b) :=
    ⟨ra, Function.update d1.stacks (leftBlock a b (outputPort ha)) wa⟩
  let d3 : State 8 (16 + a + b) :=
    ⟨readRegs d2.regs 0 1 none, Function.update d2.stacks (rightBlock a b (inputPort hb)) xs⟩
  have hd2source : d2.stacks (lowPort a b 0) = xs := by
    simp [d2, d1, hd0source ]
  have hcopyB : Eval
      (copyCmd (lowPort a b 0) (rightBlock a b (inputPort hb)) (lowPort a b 7))
      (7 * xs.length + 5) d2 d3 := by
    have h :=
      copy_eval (lowPort a b 0) (rightBlock a b (inputPort hb)) (lowPort a b 7) d2
        (by simp) (by simp) (by simp)
        (by simp [d2, d1, d0, initial_stacks ])
        (by simp [d2, d1, d0, initial_stacks, inputPort, htmp0 ])
    rw [hd2source] at h
    simpa only [d3] using h
  have hcleanB : d3.stacks ∘ rightBlock a b = (state hb d3.regs xs []).stacks := by
    funext i
    simp [d3, d2, d1, d0, initial_stacks, Function.comp_apply,
      Function.update_apply, (rightBlock a b).injective.eq_iff ]
  obtain ⟨nb, wb, rb, heB, hvB, hwB, htB⟩ := block_eval hcb (rightBlock a b) d3 xs hcleanB
  let d4 : State 8 (16 + a + b) :=
    ⟨rb, Function.update d3.stacks (rightBlock a b (outputPort hb)) wb⟩
  have hlow10 : lowPort a b 1 ≠ (0 : Fin (16 + a + b)) := by
    intro h
    have := congrArg Fin.val h
    simp [lowPort] at this
  have hvalid : ArithmeticCalls.Valid (binaryPorts a b ha hb) d4 := by
    constructor
    · simp [d4, d3, d2, d1, d0, initial_stacks, inputPort, binaryPorts,
        hlow10 ]
    · intro i
      have hwli : workBlock a b i ≠ leftBlock a b (inputPort ha) :=
        (left_ne_low a b (inputPort ha) ⟨i.val + 2, by omega⟩).symm
      have hwlo : workBlock a b i ≠ leftBlock a b (outputPort ha) :=
        (left_ne_low a b (outputPort ha) ⟨i.val + 2, by omega⟩).symm
      have hwri : workBlock a b i ≠ rightBlock a b (inputPort hb) :=
        (right_ne_low a b (inputPort hb) ⟨i.val + 2, by omega⟩).symm
      have hwro : workBlock a b i ≠ rightBlock a b (outputPort hb) :=
        (right_ne_low a b (outputPort hb) ⟨i.val + 2, by omega⟩).symm
      have hwparent : workBlock a b i ≠ lowPort a b 0 := by
        intro h
        have hv := congrArg Fin.val h
        change i.val + 2 = 0 at hv
        omega
      have hwzero : workBlock a b i ≠ (0 : Fin (16 + a + b)) := hwparent
      simp [d4, d3, d2, d1, d0, initial_stacks, binaryPorts,
        hwli, hwlo, hwri, hwro ]
  have hleft : d4.stacks (binaryPorts a b ha hb).left = wa := by
    simp [d4, d3, d2, d1, binaryPorts]
  have hright : d4.stacks (binaryPorts a b ha hb).right = wb := by
    simp [d4, binaryPorts]
  have harith : ∃ nt rf word,
      Eval (if isMul then ArithmeticCalls.multiplyAt (binaryPorts a b ha hb)
        else ArithmeticCalls.addAt (binaryPorts a b ha hb)) nt d4
        ⟨rf, Function.update d4.stacks (lowPort a b 1) word⟩ ∧
      BinaryArithmetic.toNat word = (if isMul then
        BinaryArithmetic.toNat wa * BinaryArithmetic.toNat wb else
        BinaryArithmetic.toNat wa + BinaryArithmetic.toNat wb) ∧
      word.length ≤ wa.length + wb.length + 1 ∧
      nt ≤ 100 * (wa.length + wb.length + 1)^2 := by
    cases isMul with
    | false =>
        obtain ⟨t, r, w, he, hv, hw, ht⟩ :=
          ArithmeticCalls.addAt_eval (binaryPorts a b ha hb) d4 hvalid
        rw [hleft, hright] at hv hw ht
        exact ⟨t, r, w, he, hv, hw, ht⟩
    | true =>
        obtain ⟨t, r, w, he, hv, hw, ht⟩ :=
          ArithmeticCalls.multiplyAt_eval (binaryPorts a b ha hb) d4 hvalid
        rw [hleft, hright] at hv hw ht
        exact ⟨t, r, w, he, hv, hw, ht⟩
  obtain ⟨nt, rf, word, heT, hvT, hwT, htT⟩ := harith
  let d5 : State 8 (16 + a + b) := ⟨rf, Function.update d4.stacks (lowPort a b 1) word⟩
  let d6 : State 8 (16 + a + b) :=
    ⟨readRegs d5.regs 0 1 none, Function.update d5.stacks (rightBlock a b (outputPort hb)) []⟩
  let d7 : State 8 (16 + a + b) :=
    ⟨readRegs d6.regs 0 1 none, Function.update d6.stacks (rightBlock a b (inputPort hb)) []⟩
  let d8 : State 8 (16 + a + b) :=
    ⟨readRegs d7.regs 0 1 none, Function.update d7.stacks (leftBlock a b (outputPort ha)) []⟩
  let d9 : State 8 (16 + a + b) :=
    ⟨readRegs d8.regs 0 1 none, Function.update d8.stacks (leftBlock a b (inputPort ha)) []⟩
  have hcB1 : Eval (clearCmd (rightBlock a b (outputPort hb))) (2 * wb.length + 3) d5 d6 := by
    simpa [d6, d5, d4] using clear_eval (rightBlock a b (outputPort hb)) d5
  have hcB0 : Eval (clearCmd (rightBlock a b (inputPort hb))) (2 * xs.length + 3) d6 d7 := by
    simpa [d7, d6, d5, d4, d3, (rightBlock a b).injective.eq_iff] using
      clear_eval (rightBlock a b (inputPort hb)) d6
  have hcA1 : Eval (clearCmd (leftBlock a b (outputPort ha))) (2 * wa.length + 3) d7 d8 := by
    simpa [d8, d7, d6, d5, d4, d3, d2] using
      clear_eval (leftBlock a b (outputPort ha)) d7
  have hcA0 : Eval (clearCmd (leftBlock a b (inputPort ha))) (2 * xs.length + 3) d8 d9 := by
    simpa [d9, d8, d7, d6, d5, d4, d3, d2, d1, (leftBlock a b).injective.eq_iff] using
      clear_eval (leftBlock a b (inputPort ha)) d8
  have hend : d9 = state hp d9.regs xs word := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      simp only [d8, d7, d6, d5, d4, d3, d2, d1, d0,
        parent_input, state, parent_output, Function.update_apply]
      split_ifs <;> simp_all
  let n := na + nb + 18 * xs.length + 2 * wa.length + 2 * wb.length + 24 + nt
  have hrun : Eval (binaryCmd ha hb isMul ca cb) n d0 d9 := by
    have hseq := Eval.seq hcopyA (Eval.seq heA (Eval.seq hcopyB (Eval.seq heB
      (Eval.seq heT (Eval.seq hcB1 (Eval.seq hcB0 (Eval.seq hcA1 hcA0)))))))
    convert hseq using 1
    dsimp [binaryCmd, n]
    omega
  refine ⟨n, word, d9.regs, ?_, ?_, ?_, ?_⟩
  · rw [← hend]
    exact hrun
  · rw [hvT, hvA, hvB]
    cases isMul <;> rfl
  · have hw := hwT.trans (ArithmeticExpressionBounds.width_bound hwA hwB)
    cases isMul <;> simpa only [Bool.false_eq_true, ↓reduceIte, widthCoeff] using hw
  · have htime := ArithmeticExpressionBounds.binary_cost_bound
      (K := 100) hwA hwB htA htB
    have htotal : n ≤ (timeCoeff ea + timeCoeff eb +
        100 * (widthCoeff ea + widthCoeff eb + 1)^2 +
        100 * (widthCoeff ea + widthCoeff eb + 1)) * (xs.length + 1)^2 := by
      dsimp [n]
      omega
    cases isMul <;> simpa only [Bool.false_eq_true, ↓reduceIte, timeCoeff] using htotal


theorem unary_spec {e : Expr} {a : ℕ} (ha : 2 ≤ a) (ca : Cmd 8 a)
    (hc : Spec e ha ca) : Spec (.pred e) (by omega) (unaryCmd ha ca) := by
  intro xs regs
  let d0 : State 8 (16 + a) := state (by omega) regs xs []
  let ci := leftBlock a 0 (inputPort ha)
  let co := leftBlock a 0 (outputPort ha)
  let ip := lowPort a 0 0
  let op := lowPort a 0 1
  let tmp := lowPort a 0 7
  have hciip : ci ≠ ip := left_ne_low a 0 (inputPort ha) 0
  have hcoop : co ≠ op := left_ne_low a 0 (outputPort ha) 1
  have hcitmp : ci ≠ tmp := left_ne_low a 0 (inputPort ha) 7
  have hcotmp : co ≠ tmp := left_ne_low a 0 (outputPort ha) 7
  have hciop : ci ≠ op := left_ne_low a 0 (inputPort ha) 1
  have hcoip : co ≠ ip := left_ne_low a 0 (outputPort ha) 0
  have hcico : ci ≠ co := by
    intro h
    exact input_ne_output ha ((leftBlock a 0).injective h)
  have hiptmp : ip ≠ tmp := by
    intro h
    have h' : (0 : ℕ) = 7 := congrArg Fin.val h
    omega
  have hopip : op ≠ ip := by simp [op, ip, lowPort, Fin.ext_iff]
  have htmpop : tmp ≠ op := by
    intro h
    have h' : (7 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hip : inputPort (show 2 ≤ 16 + a by omega) = ip := rfl
  have hop : outputPort (show 2 ≤ 16 + a by omega) = op := rfl
  have hd0ip : d0.stacks ip = xs := by
    rw [← hip]
    exact state_input _ _ _ _
  have hd0ci : d0.stacks ci = [] := by simp [d0, state, hip, hop, hciip, hciop]
  have hd0tmp : d0.stacks tmp = [] := by
    simp [d0, state, hip, hop, hiptmp.symm, htmpop]
  have hc1 := copy_eval ip ci tmp d0 hciip.symm hiptmp hcitmp.symm hd0ci hd0tmp
  let d1 : State 8 (16 + a) :=
    ⟨readRegs d0.regs 0 1 none, Function.update d0.stacks ci xs⟩
  have hc1' : Eval (copyCmd ip ci tmp) (7 * xs.length + 5) d0 d1 := by
    simpa [d1, hd0ip] using hc1
  have clean : d1.stacks ∘ leftBlock a 0 = (state ha d1.regs xs []).stacks := by
    funext i
    have hparent : d0.stacks (leftBlock a 0 i) = [] := by
      apply state_other (i := leftBlock a 0 i)
        (h := by omega) (regs := regs) (input := xs) (output := [])
      · exact left_ne_parent_input a 0 (by omega) i
      · exact left_ne_parent_output a 0 (by omega) i
    simp only [d1, Function.comp_apply, Function.update_apply]
    by_cases hci : leftBlock a 0 i = ci
    · rw [ite_eq_left hci]
      have hi : i = inputPort ha := (leftBlock a 0).injective hci
      subst i
      exact (state_input ha d1.regs xs []).symm
    · rw [ite_eq_right hci, hparent]
      have hi : i ≠ inputPort ha := by
        intro hi
        subst i
        exact hci rfl
      by_cases ho : i = outputPort ha
      · subst i
        exact (state_output ha d1.regs xs []).symm
      · exact (state_other ha d1.regs xs [] i hi ho).symm
  obtain ⟨n, word, rf, hchild, hvalue, hwidth, htime⟩ :=
    block_eval hc (leftBlock a 0) d1 xs clean
  let d2 : State 8 (16 + a) := ⟨rf, Function.update d1.stacks co word⟩
  have hd2co : d2.stacks co = word := by simp [d2]
  have hd2op : d2.stacks op = [] := by
    simp [d2, d1, d0, state, hip, hop, hcoop.symm, hciop.symm]
  have hd2tmp : d2.stacks tmp = [] := by
    simp [d2, d1, hcotmp.symm, hcitmp.symm, hd0tmp]
  have hc2 := copy_eval co op tmp d2 hcoop hcotmp htmpop hd2op hd2tmp
  let d3 : State 8 (16 + a) :=
    ⟨readRegs d2.regs 0 1 none, Function.update d2.stacks op word⟩
  have hc2' : Eval (copyCmd co op tmp) (7 * word.length + 5) d2 d3 := by
    simpa [d3, hd2co] using hc2
  have hd3scratch : d3.stacks (predPorts a).scratch = [] := by
    have hsci : (predPorts a).scratch ≠ ci :=
      (left_ne_low a 0 (inputPort ha) 2).symm
    have hsco : (predPorts a).scratch ≠ co :=
      (left_ne_low a 0 (outputPort ha) 2).symm
    have hsop : (predPorts a).scratch ≠ op := by
      intro h
      have hv := congrArg Fin.val h
      change (2 : ℕ) = 1 at hv
      omega
    have hsip : (predPorts a).scratch ≠ ip := by
      intro h
      have hv := congrArg Fin.val h
      change (2 : ℕ) = 0 at hv
      omega
    simp [d3, d2, d1, d0, state, hsci, hsco, hsop, hsip, hip, hop]
  have hd3counter : d3.stacks (predPorts a).counter = word := by
    simp [d3, predPorts, op]
  obtain ⟨t, rp, out, ht, hp, hv, hw⟩ :=
    CounterPredProgram.pred_correct (predPorts a) d3 hd3scratch
  let d4 : State 8 (16 + a) := ⟨rp, Function.update d3.stacks op out⟩
  have hp' : Eval (CounterPredProgram.predCmd (predPorts a)) t d3 d4 := hp
  have hd4co : d4.stacks co = word := by
    simp [d4, d3, d2, hcoop]
  have hc3 := clear_eval co d4
  let d5 : State 8 (16 + a) :=
    ⟨readRegs d4.regs 0 1 none, Function.update d4.stacks co []⟩
  have hc3' : Eval (clearCmd co) (2 * word.length + 3) d4 d5 := by
    simpa [d5, hd4co] using hc3
  have hd5ci : d5.stacks ci = xs := by
    simp [d5, d4, d3, d2, d1, hcico, hciop]
  have hc4 := clear_eval ci d5
  let rfinal := readRegs d5.regs 0 1 none
  have hfinal : (⟨rfinal, Function.update d5.stacks ci []⟩ : State 8 (16 + a)) =
      state (by omega) rfinal xs out := by
    congr 1
    funext i
    simp [d5, d4, d3, d2, d1, d0, state, Function.update_apply, hip, hop]
    split_ifs <;> simp_all
  have hc4' : Eval (clearCmd ci) (2 * xs.length + 3) d5
      (state (by omega) rfinal xs out) := by
    change Eval (clearCmd ci) (2 * (d5.stacks ci).length + 3) d5
      (⟨rfinal, Function.update d5.stacks ci []⟩ : State 8 (16 + a)) at hc4
    rw [hfinal] at hc4
    rw [hd5ci] at hc4
    exact hc4
  let total := (7 * xs.length + 5) + ((n + 1) + ((7 * word.length + 5) +
    (t + ((2 * word.length + 3) + (2 * xs.length + 3)))))
  refine ⟨total, out, rfinal, ?_, ?_, ?_, ?_⟩
  · exact hc1'.seq (hchild.seq (hc2'.seq (hp'.seq (hc3'.seq hc4'))))
  · simpa only [hd3counter, hvalue, eval] using hv
  · have hout : out.length ≤ word.length := by simpa only [hd3counter] using hw
    simpa only [widthCoeff] using (hout.trans hwidth)
  · have ht' : t ≤ 20 * (word.length + 1) := by simpa only [hd3counter] using ht
    have htot : total ≤ n + 9 * xs.length + 29 * word.length + 40 := by
      dsimp [total]
      omega
    exact htot.trans (ArithmeticExpressionBounds.unary_cost_bound hwidth htime)



theorem command_spec (e : Expr) :
    Spec e (by have := slots_ge e; omega) (command e) := by
  induction e with
  | input => exact input_spec
  | const n => exact const_spec n
  | add a b ha hb =>
      simpa only [Bool.false_eq_true, ↓reduceIte, command, slots] using
        binary_spec (by have := slots_ge a; omega) (by have := slots_ge b; omega)
          false (command a) (command b) ha hb
  | mul a b ha hb =>
      simpa only [↓reduceIte, command, slots] using
        binary_spec (by have := slots_ge a; omega) (by have := slots_ge b; omega)
          true (command a) (command b) ha hb
  | pred a ha =>
      simpa only [command, slots] using unary_spec (by have := slots_ge a; omega) (command a) ha

def program (e : Expr) :=
  compiled (command e) (inputPort (by have := slots_ge e; omega))
    (outputPort (by have := slots_ge e; omega))

theorem program_correct (e : Expr) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
      word.length ≤ widthCoeff e * (xs.length + 1) ∧
      RunsIn (program e) (timeCoeff e * (xs.length + 1)^2 + 1)
        ((state (by have := slots_ge e; omega) regs xs []).withPC (some (program e).entry))
        ((state (by have := slots_ge e; omega) rf xs word).withPC none) := by
  obtain ⟨n, word, rf, hr, hv, hw, ht⟩ := command_spec e xs regs
  exact ⟨word, rf, hv, hw, n + 1, by omega, compiled_halt_trace hr _ _⟩

/-- The primitive simulation factor depends on the fixed expression program,
never on the input word or its numeric value. -/
theorem primitive_correct (e : Expr) (xs : List Bool) (regs : Fin 8 → Bool) :
    ∃ word rf,
      BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
      word.length ≤ widthCoeff e * (xs.length + 1) ∧
      Computation.RunsIn (primitive (program e)).step
        (primitiveOverhead (program e) * (timeCoeff e * (xs.length + 1)^2 + 1))
        (primitiveCfg (program e)
          ((state (by have := slots_ge e; omega) regs xs []).withPC (some (program e).entry)))
        (primitiveCfg (program e)
          ((state (by have := slots_ge e; omega) rf xs word).withPC none)) := by
  obtain ⟨word, rf, hv, hw, hr⟩ := program_correct e xs regs
  exact ⟨word, rf, hv, hw, BitProgram.primitive_execution (program e) hr⟩

/-- No prepared input configuration is required: the sole raw binary input
word starts on the program's designated input stack, with empty work stacks. -/
theorem raw_input_correct (e : Expr) (xs : List Bool) :
    ∃ word rf,
      BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
      word.length ≤ widthCoeff e * (xs.length + 1) ∧
      RunsIn (program e) (timeCoeff e * (xs.length + 1)^2 + 1)
        (initial (program e) xs)
        ((state (by have := slots_ge e; omega) rf xs word).withPC none) := by
  obtain ⟨word, rf, hv, hw, hr⟩ := program_correct e xs (fun _ => false)
  refine ⟨word, rf, hv, hw, ?_⟩
  have hi : (state (by have := slots_ge e; omega) (fun _ => false) xs []).withPC
      (some (program e).entry) = initial (program e) xs := by
    unfold initial StructuredProgram.State.withPC
    congr 1
    rw [initial_stacks]
    funext i
    simp only [Function.update_apply, program, compiled]
    rfl
  rwa [hi] at hr

theorem raw_primitive_correct (e : Expr) (xs : List Bool) :
    ∃ word rf,
      BinaryArithmetic.toNat word = eval (BinaryArithmetic.toNat xs) e ∧
      word.length ≤ widthCoeff e * (xs.length + 1) ∧
      Computation.RunsIn (primitive (program e)).step
        (primitiveOverhead (program e) * (timeCoeff e * (xs.length + 1)^2 + 1))
        ((primitive (program e)).init xs)
        (primitiveCfg (program e)
          ((state (by have := slots_ge e; omega) rf xs word).withPC none)) := by
  obtain ⟨word, rf, hv, hw, hr⟩ := raw_input_correct e xs
  refine ⟨word, rf, hv, hw, ?_⟩
  simpa only [primitive_initial] using BitProgram.primitive_execution (program e) hr

end SubexponentialSAT.ArithmeticExpressionProgram

end OAI.Algorithms
