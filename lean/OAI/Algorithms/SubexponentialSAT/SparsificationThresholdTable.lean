import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationThresholdProgram

namespace OAI.Algorithms

/-!
# Statically compiled threshold banks

Every arithmetic expression and output port is fixed before the input M is
read. The common arithmetic workspace is reused, while completed outputs are
stored in a disjoint fixed bank.
-/

namespace SubexponentialSAT.SparsificationThresholdTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open scoped BigOperators


def workSlots {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : ℕ :=
  16 + ∑ i, ArithmeticExpressionProgram.slots (es i)

theorem workSlots_ge {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : 16 ≤ workSlots es := by
  unfold workSlots
  omega

theorem child_le_work {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) :
    ArithmeticExpressionProgram.slots (es i) ≤ workSlots es := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (ArithmeticExpressionProgram.slots (es j)))
    (Finset.mem_univ i)
  exact h.trans (by unfold workSlots; omega)

def workInput {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : Fin (workSlots es) :=
  ArithmeticExpressionProgram.inputPort (by have := workSlots_ge es; omega)
def workOutput {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : Fin (workSlots es) :=
  ArithmeticExpressionProgram.outputPort (by have := workSlots_ge es; omega)
def workScratch {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : Fin (workSlots es) :=
  ⟨2, by have := workSlots_ge es; omega⟩

def inputPort {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : Fin (workSlots es + n) :=
  Fin.castAdd n (workInput es)
def pendingPort {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : Fin (workSlots es + n) :=
  Fin.castAdd n (workOutput es)
def scratchPort {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : Fin (workSlots es + n) :=
  Fin.castAdd n (workScratch es)
def bankPort {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) : Fin (workSlots es + n) :=
  Fin.natAdd (workSlots es) i

@[simp] theorem inputPort_val {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) :
    (inputPort es).val = 0 := rfl

@[simp] theorem bankPort_val {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) :
    (bankPort es i).val = workSlots es + i.val := rfl

def state {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending : List Bool) (outputs : Fin n → List Bool) : State 8 (workSlots es + n) :=
  ⟨r, Fin.append
    (ArithmeticExpressionProgram.state (by have := workSlots_ge es; omega) r xs pending).stacks outputs⟩

@[simp] theorem state_input {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending : List Bool) (outputs : Fin n → List Bool) :
    (state es r xs pending outputs).stacks (inputPort es) = xs := by
  simp [state, inputPort, workInput]

@[simp] theorem state_pending {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending : List Bool) (outputs : Fin n → List Bool) :
    (state es r xs pending outputs).stacks (pendingPort es) = pending := by
  simp [state, pendingPort, workOutput]

@[simp] theorem state_bank {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending : List Bool) (outputs : Fin n → List Bool) (i : Fin n) :
    (state es r xs pending outputs).stacks (bankPort es i) = outputs i := by
  simp [state, bankPort]

@[simp] theorem state_scratch {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending : List Bool) (outputs : Fin n → List Bool) :
    (state es r xs pending outputs).stacks (scratchPort es) = [] := by
  simp only [state, scratchPort, Fin.append_left]
  simp [workScratch, ArithmeticExpressionProgram.state, ArithmeticExpressionProgram.inputPort, ArithmeticExpressionProgram.outputPort, Fin.ext_iff]

theorem work_ne_bank {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr)
    (j : Fin (workSlots es)) (i : Fin n) :
    Fin.castAdd n j ≠ bankPort es i := by
  intro h
  have hv := congrArg Fin.val h
  change j.val = workSlots es + i.val at hv
  omega

theorem pending_ne_scratch {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) :
    pendingPort es ≠ scratchPort es := by
  intro h
  have hv := congrArg Fin.val h
  simp [pendingPort, scratchPort, workOutput, workScratch, ArithmeticExpressionProgram.outputPort] at hv

theorem update_append_left {a b : ℕ} {α : Type*}
    (f : Fin a → α) (g : Fin b → α) (i : Fin a) (x : α) :
    Function.update (Fin.append f g) (Fin.castAdd b i) x =
      Fin.append (Function.update f i x) g := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun r => ?_) j
  · simp [Function.update_apply, Fin.ext_iff]
  · have hn : Fin.natAdd a r ≠ Fin.castAdd b i := by
      intro h
      have hv := congrArg Fin.val h
      change a + r.val = i.val at hv
      omega
    simp [hn]

theorem update_append_right {a b : ℕ} {α : Type*}
    (f : Fin a → α) (g : Fin b → α) (i : Fin b) (x : α) :
    Function.update (Fin.append f g) (Fin.natAdd a i) x =
      Fin.append f (Function.update g i x) := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun r => ?_) j
  · have hn : Fin.castAdd b l ≠ Fin.natAdd a i := by
      intro h
      have hv := congrArg Fin.val h
      change l.val = a + i.val at hv
      omega
    simp [hn]
  · simp [Function.update_apply, Fin.ext_iff]

theorem update_state_pending {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending word : List Bool) (outputs : Fin n → List Bool) :
    Function.update (state es r xs pending outputs).stacks (pendingPort es) word =
      (state es r xs word outputs).stacks := by
  rw [state, pendingPort, update_append_left]
  simp only [state, ArithmeticExpressionProgram.state, workOutput, Function.update_idem]

theorem update_state_bank {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (r : Fin 8 → Bool)
    (xs pending word : List Bool) (outputs : Fin n → List Bool) (i : Fin n) :
    Function.update (state es r xs pending outputs).stacks (bankPort es i) word =
      (state es r xs pending (Function.update outputs i word)).stacks := by
  exact update_append_right _ _ _ _

def childWork {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) :
    Fin (ArithmeticExpressionProgram.slots (es i)) ↪ Fin (workSlots es) where
  toFun j := ⟨j.val, lt_of_lt_of_le j.isLt (child_le_work es i)⟩
  inj' := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun p : Fin (workSlots es) => p.val) h

def childBlock {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) :
    Fin (ArithmeticExpressionProgram.slots (es i)) ↪ Fin (workSlots es + n) where
  toFun j := Fin.castAdd n (childWork es i j)
  inj' := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun p : Fin (workSlots es + n) => p.val) h

theorem child_output {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) :
    childBlock es i (ArithmeticExpressionProgram.outputPort (by have := ArithmeticExpressionProgram.slots_ge (es i); omega)) =
      pendingPort es := by
  apply Fin.ext
  rfl

theorem local_state_restrict {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n)
    (r : Fin 8 → Bool) (xs pending : List Bool) (outputs : Fin n → List Bool) :
    (ArithmeticExpressionProgram.state (by have := ArithmeticExpressionProgram.slots_ge (es i); omega) r xs pending).stacks =
      (state es r xs pending outputs).stacks ∘ childBlock es i := by
  funext j
  change (ArithmeticExpressionProgram.state
    (by have := ArithmeticExpressionProgram.slots_ge (es i); omega) r xs pending).stacks j =
    Fin.append (ArithmeticExpressionProgram.state
      (by have := workSlots_ge es; omega) r xs pending).stacks outputs
        (Fin.castAdd n (childWork es i j))
  rw [Fin.append_left]
  have hv : (childWork es i j).val = j.val := rfl
  simp [ArithmeticExpressionProgram.state, ArithmeticExpressionProgram.inputPort,
    ArithmeticExpressionProgram.outputPort, Function.update_apply, Fin.ext_iff, hv]

abbrev evaluateOne {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) :
    Cmd 8 (workSlots es + n) :=
  .call (ProgramLinking.liftProgram (ArithmeticExpressionProgram.program (es i)) id (childBlock es i))

theorem evaluateOne_eval {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n)
    (r : Fin 8 → Bool) (xs : List Bool) (outputs : Fin n → List Bool) :
    ∃ steps word rf,
      Eval (evaluateOne es i) steps (state es r xs [] outputs) (state es rf xs word outputs) ∧
      BinaryArithmetic.toNat word = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
      word.length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1) ∧
      steps ≤ ArithmeticExpressionProgram.timeCoeff (es i) * (xs.length + 1)^2 + 1 := by
  obtain ⟨steps, word, rf, hr, hv, hw, ht⟩ := ArithmeticExpressionProgram.command_spec (es i) xs r
  have hcall := ArithmeticExpressionSupport.call_on_block (ArithmeticExpressionProgram.command (es i))
    (ArithmeticExpressionProgram.inputPort (by have := ArithmeticExpressionProgram.slots_ge (es i); omega))
    (ArithmeticExpressionProgram.outputPort (by have := ArithmeticExpressionProgram.slots_ge (es i); omega))
    (childBlock es i) (state es r xs [] outputs) _ _ word hr rfl
    (local_state_restrict es i r xs [] outputs) (by
      simp [ArithmeticExpressionProgram.state, Function.update_idem])
  rw [child_output, update_state_pending] at hcall
  exact ⟨steps + 1, word, rf, hcall, hv, hw, by omega⟩

abbrev row {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) : Cmd 8 (workSlots es + n) :=
  .seq (evaluateOne es i)
    (.seq (ArithmeticExpressionSupport.copyCmd (pendingPort es) (bankPort es i) (scratchPort es))
      (ArithmeticExpressionSupport.clearCmd (pendingPort es)))

def rowCoeff {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n) : ℕ :=
  ArithmeticExpressionProgram.timeCoeff (es i) + 9 * ArithmeticExpressionProgram.widthCoeff (es i) + 9

theorem row_eval {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) (i : Fin n)
    (r : Fin 8 → Bool) (xs : List Bool) (outputs : Fin n → List Bool)
    (hempty : outputs i = []) :
    ∃ steps word rf,
      Eval (row es i) steps (state es r xs [] outputs)
        (state es rf xs [] (Function.update outputs i word)) ∧
      BinaryArithmetic.toNat word = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
      word.length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1) ∧
      steps ≤ rowCoeff es i * (xs.length + 1)^2 := by
  obtain ⟨steps, word, rf, hr, hv, hw, ht⟩ := evaluateOne_eval es i r xs outputs
  have hcopy := ArithmeticExpressionSupport.copy_eval (pendingPort es) (bankPort es i) (scratchPort es)
    (state es rf xs word outputs) (work_ne_bank es _ i) (pending_ne_scratch es)
    (work_ne_bank es _ i) (by simpa using hempty) (by simp)
  rw [state_pending, update_state_bank] at hcopy
  let r₁ := readRegs rf 0 1 none
  have hcopy' : Eval (ArithmeticExpressionSupport.copyCmd (pendingPort es) (bankPort es i) (scratchPort es))
      (7 * word.length + 5) (state es rf xs word outputs)
      (state es r₁ xs word (Function.update outputs i word)) := hcopy
  have hclear := ArithmeticExpressionSupport.clear_eval (pendingPort es)
    (state es r₁ xs word (Function.update outputs i word))
  rw [state_pending, update_state_pending] at hclear
  let r₂ := readRegs r₁ 0 1 none
  have hclear' : Eval (ArithmeticExpressionSupport.clearCmd (pendingPort es)) (2 * word.length + 3)
      (state es r₁ xs word (Function.update outputs i word))
      (state es r₂ xs [] (Function.update outputs i word)) := hclear
  refine ⟨steps + ((7 * word.length + 5) + (2 * word.length + 3)),
    word, r₂, .seq hr (.seq hcopy' hclear'), hv, hw, ?_⟩
  have hsq : xs.length + 1 ≤ (xs.length + 1)^2 := by nlinarith
  have hpos : 1 ≤ (xs.length + 1)^2 := by nlinarith
  have hw9 := Nat.mul_le_mul_left 9 hw
  have hlin := Nat.mul_le_mul_left (9 * ArithmeticExpressionProgram.widthCoeff (es i)) hsq
  have hc := Nat.mul_le_mul_left 9 hpos
  unfold rowCoeff
  nlinarith

/-- This recursion builds finite syntax before the input word is supplied. -/
def sequence {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) :
    List (Fin n) → Cmd 8 (workSlots es + n)
  | [] => .base .skip
  | i :: rest => .seq (row es i) (sequence es rest)

def sequenceCoeff {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) :
    List (Fin n) → ℕ
  | [] => 0
  | i :: rest => rowCoeff es i + sequenceCoeff es rest

theorem sequence_eval {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr)
    (indices : List (Fin n)) (hnd : indices.Nodup)
    (r : Fin 8 → Bool) (xs : List Bool) (outputs : Fin n → List Bool)
    (hempty : ∀ i ∈ indices, outputs i = []) :
    ∃ steps rf results,
      Eval (sequence es indices) steps (state es r xs [] outputs) (state es rf xs [] results) ∧
      steps ≤ sequenceCoeff es indices * (xs.length + 1)^2 ∧
      (∀ i ∈ indices,
        BinaryArithmetic.toNat (results i) = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
        (results i).length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1)) ∧
      (∀ i ∉ indices, results i = outputs i) := by
  induction indices generalizing r outputs with
  | nil =>
      exact ⟨0, r, outputs, .base (.skip _), by simp [sequenceCoeff],
        by simp, by simp⟩
  | cons i rest ih =>
      obtain ⟨hi, hrest⟩ := List.nodup_cons.mp hnd
      obtain ⟨a, word, middle, ha, hv, hl, hac⟩ :=
        row_eval es i r xs outputs (hempty i (by simp))
      have hm : ∀ j ∈ rest, (Function.update outputs i word) j = [] := by
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        simpa [hji] using hempty j (by simp [hj])
      obtain ⟨b, rf, results, hb, hbc, hvalues, hframe⟩ :=
        ih hrest middle (Function.update outputs i word) hm
      refine ⟨a + b, rf, results, .seq ha hb, ?_, ?_, ?_⟩
      · calc
          a + b ≤ rowCoeff es i * (xs.length + 1)^2 +
              sequenceCoeff es rest * (xs.length + 1)^2 := Nat.add_le_add hac hbc
          _ = sequenceCoeff es (i :: rest) * (xs.length + 1)^2 := by
            simp only [sequenceCoeff, Nat.add_mul]
      · intro j hj
        rcases List.mem_cons.mp hj with hji | hjr
        · subst j
          rw [hframe i hi, Function.update_self]
          exact ⟨hv, hl⟩
        · exact hvalues j hjr
      · intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hj (by simp)
        have hjr : j ∉ rest := by intro h; exact hj (by simp [h])
        rw [hframe j hjr, Function.update_of_ne hji]

abbrev command {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) :
    Cmd 8 (workSlots es + n) := sequence es (List.finRange n)

def timeCoeff {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : ℕ :=
  sequenceCoeff es (List.finRange n) + 1

def widthCoeff {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) : ℕ :=
  ∑ i, ArithmeticExpressionProgram.widthCoeff (es i)

theorem command_eval {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr)
    (r : Fin 8 → Bool) (xs : List Bool) :
    ∃ steps rf results,
      Eval (command es) steps (state es r xs [] (fun _ => [])) (state es rf xs [] results) ∧
      steps + 1 ≤ timeCoeff es * (xs.length + 1)^2 ∧
      (∀ i, BinaryArithmetic.toNat (results i) = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
        (results i).length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1)) ∧
      (∑ i, (results i).length) ≤ widthCoeff es * (xs.length + 1) := by
  obtain ⟨steps, rf, results, hr, hc, hv, _⟩ :=
    sequence_eval es (List.finRange n) (List.nodup_finRange n) r xs (fun _ => [])
      (by simp)
  have hvals : ∀ i, BinaryArithmetic.toNat (results i) =
        ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
      (results i).length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1) :=
    fun i => hv i (List.mem_finRange i)
  refine ⟨steps, rf, results, hr, ?_, hvals, ?_⟩
  · have hpos : 1 ≤ (xs.length + 1)^2 := by
      simpa using Nat.pow_le_pow_left (show 1 ≤ xs.length + 1 by omega) 2
    calc
      steps + 1 ≤ sequenceCoeff es (List.finRange n) * (xs.length + 1)^2 +
          (xs.length + 1)^2 := Nat.add_le_add hc hpos
      _ = timeCoeff es * (xs.length + 1)^2 := by unfold timeCoeff; ring
  · calc
      (∑ i, (results i).length) ≤
          ∑ i, ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1) :=
        Finset.sum_le_sum (fun i _ => (hvals i).2)
      _ = widthCoeff es * (xs.length + 1) := by
        simp only [widthCoeff, Finset.sum_mul]

def program {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr) :=
  compiled (command es) (inputPort es) (inputPort es)

theorem program_correct {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr)
    (r : Fin 8 → Bool) (xs : List Bool) :
    ∃ rf results,
      RunsIn (program es) (timeCoeff es * (xs.length + 1)^2)
        ((state es r xs [] (fun _ => [])).withPC (some (program es).entry))
        ((state es rf xs [] results).withPC none) ∧
      (∀ i, BinaryArithmetic.toNat (results i) = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
        (results i).length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1)) ∧
      (∑ i, (results i).length) ≤ widthCoeff es * (xs.length + 1) := by
  obtain ⟨steps, rf, results, hr, hc, hv, hw⟩ := command_eval es r xs
  exact ⟨rf, results, ⟨steps + 1, hc, compiled_halt_trace hr _ _⟩, hv, hw⟩

theorem call_eval {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr)
    (r : Fin 8 → Bool) (xs : List Bool) :
    ∃ steps rf results,
      Eval (.call (program es)) steps
        (state es r xs [] (fun _ => [])) (state es rf xs [] results) ∧
      steps ≤ timeCoeff es * (xs.length + 1)^2 ∧
      (∀ i, BinaryArithmetic.toNat (results i) = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
        (results i).length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1)) ∧
      (∑ i, (results i).length) ≤ widthCoeff es * (xs.length + 1) := by
  obtain ⟨rf, results, ⟨steps, hc, hr⟩, hv, hw⟩ := program_correct es r xs
  exact ⟨steps, rf, results, .call (program es) hr, hc, hv, hw⟩

theorem primitive_correct {n : ℕ} (es : Fin n → ArithmeticExpressionProgram.Expr)
    (r : Fin 8 → Bool) (xs : List Bool) :
    ∃ rf results,
      Computation.RunsIn (primitive (program es)).step
        (primitiveOverhead (program es) * (timeCoeff es * (xs.length + 1)^2))
        (primitiveCfg (program es)
          ((state es r xs [] (fun _ => [])).withPC (some (program es).entry)))
        (primitiveCfg (program es) ((state es rf xs [] results).withPC none)) ∧
      (∀ i, BinaryArithmetic.toNat (results i) = ArithmeticExpressionProgram.eval (BinaryArithmetic.toNat xs) (es i) ∧
        (results i).length ≤ ArithmeticExpressionProgram.widthCoeff (es i) * (xs.length + 1)) ∧
      (∑ i, (results i).length) ≤ widthCoeff es * (xs.length + 1) := by
  obtain ⟨rf, results, hr, hv, hw⟩ := program_correct es r xs
  exact ⟨rf, results, BitProgram.primitive_execution _ hr, hv, hw⟩

/-- There is one saved threshold per width 2,...,k. -/
def expressions (k : ℕ) : Fin (k - 1) → ArithmeticExpressionProgram.Expr :=
  fun i => SparsificationThresholdProgram.thresholdExpr (i.val + 2)

def thresholdProgram (k : ℕ) := program (expressions k)

def thresholdPort (k d : ℕ) (hd : 2 ≤ d) (hk : d ≤ k) :
    Fin (workSlots (expressions k) + (k - 1)) :=
  bankPort (expressions k) ⟨d - 2, by omega⟩

@[simp] theorem thresholdPort_val (k d : ℕ) (hd : 2 ≤ d) (hk : d ≤ k) :
    (thresholdPort k d hd hk).val = workSlots (expressions k) + (d - 2) := rfl

theorem thresholdProgram_correct (k : ℕ) (r : Fin 8 → Bool) (xs : List Bool) :
    ∃ rf results,
      RunsIn (thresholdProgram k) (timeCoeff (expressions k) * (xs.length + 1)^2)
        ((state (expressions k) r xs [] (fun _ => [])).withPC (some (thresholdProgram k).entry))
        ((state (expressions k) rf xs [] results).withPC none) ∧
      (∀ i : Fin (k - 1),
        BinaryArithmetic.toNat (results i) =
          SparsificationConstants.z (BinaryArithmetic.toNat xs) (i.val + 2) ∧
        (results i).length ≤ ArithmeticExpressionProgram.widthCoeff
          (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) * (xs.length + 1)) ∧
      (∑ i, (results i).length) ≤ widthCoeff (expressions k) * (xs.length + 1) := by
  simpa only [thresholdProgram, expressions, SparsificationThresholdProgram.eval_thresholdExpr] using
    program_correct (expressions k) r xs

end SubexponentialSAT.SparsificationThresholdTable

end OAI.Algorithms
