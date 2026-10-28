import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgminBootstrap

namespace OAI.Algorithms

/-! Unseeded binary argmin. The first mass evaluation, first score copy and
all remaining candidate evaluations are paid by the same finite program. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {r s : ℕ}

abbrev installProgram := compiled BinaryArgmin.installFirst 8 2

abbrev install (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram installProgram p.register p.stack)

theorem install_eval (p : Ports r s) (frame : State r s)
    (B C : ℕ) (next : Entry) (queue : List Bool) (regs : Fin 8 → Bool)
    (hn : BinaryArgmin.Fits B C next) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ regs',
      Eval (install p) n (state p frame regs next BinaryArgmin.empty queue)
        (state p frame regs' BinaryArgmin.empty next queue) := by
  obtain ⟨n, hn', regs', ht⟩ := BinaryArgmin.installFirst_eval B C next queue regs hn
  exact ⟨n + 1, Nat.add_le_add_right hn' 1, regs',
    eval_call_lifted installProgram p.register p.stack frame
      p.register_injective p.stack_injective (compiled_halt_trace ht 8 2)⟩

abbrev select (p : Ports r s) (mass : Cmd r s) : Cmd r s :=
  .seq (load p mass) (.ite (p.register 7)
    (.seq (install p) (.seq (scan p mass) (flag p))) (.base .skip))

def selectBudget (B C cost count : ℕ) : ℕ :=
  (count + 1) * (loadBudget C cost + 100 * (B + C + 1) + 4)

theorem select_nil (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = false ∧
      Eval (select p mass) 5
        (state p frame regs BinaryArgmin.empty BinaryArgmin.empty [false])
        (state p frame regs' BinaryArgmin.empty BinaryArgmin.empty []) := by
  obtain ⟨regs', hf, ht⟩ := load_nil p mass frame BinaryArgmin.empty regs
  exact ⟨regs', hf, Eval.seq ht
    (Eval.ite_false (by simpa using hf) (Eval.base (.skip _)))⟩

theorem select_cons (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p frame score valid B C cost)
    (seed : List Bool) (rest : List (List Bool)) (regs : Fin 8 → Bool)
    (hp : ∀ bits ∈ seed :: rest, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B) :
    ∃ n ≤ selectBudget B C cost (rest.length + 1), ∃ regs', regs' 7 = true ∧
      Eval (select p mass) n
        (state p frame regs BinaryArgmin.empty BinaryArgmin.empty
          (candidateEncoding (seed :: rest)))
        (state p frame regs' BinaryArgmin.empty
          (HashSelect.best BinaryArgmin.value (scored score seed)
            (rest.map (scored score))) []) := by
  have hs := hp seed (by simp)
  have hr : ∀ bits ∈ rest, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B :=
    fun bits h => hp bits (by simp [h])
  have hfit : BinaryArgmin.Fits B C (scored score seed) := ⟨hs.2.2, hs.2.1⟩
  obtain ⟨l, hl, regs₁, ht, he⟩ := load_cons p mass frame score valid B C cost
    hmass seed rest BinaryArgmin.empty regs hs.1 hs.2.1
  obtain ⟨i, hi, regs₂, he₂⟩ := install_eval p frame B C (scored score seed)
    (candidateEncoding rest) regs₁ hfit
  obtain ⟨t, ht', regs₃, _, he₃⟩ := scan_eval p mass frame score valid B C cost
    hmass (scored score seed) rest regs₂ hfit hr
  refine ⟨l + ((i + (t + 2)) + 1), ?_, Function.update regs₃ 7 true, by simp, ?_⟩
  · unfold selectBudget scanBudget at *
    nlinarith
  · exact Eval.seq he (Eval.ite_true (by simpa using ht)
      (Eval.seq he₂ (Eval.seq he₃ (flag_eval p frame regs₃ _ _ _))))

abbrev selectProgram (p : Ports r s) (mass : Cmd r s) :=
  compiled (select p mass) (p.stack 8) (p.stack 2)

theorem selectProgram_trace (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p frame score valid B C cost)
    (seed : List Bool) (rest : List (List Bool)) (regs : Fin 8 → Bool)
    (hp : ∀ bits ∈ seed :: rest, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B) :
    ∃ n ≤ selectBudget B C cost (rest.length + 1) + 1, ∃ regs',
      Trace (selectProgram p mass) n
        ((state p frame regs BinaryArgmin.empty BinaryArgmin.empty
          (candidateEncoding (seed :: rest))).withPC (some (selectProgram p mass).entry))
        ((state p frame regs' BinaryArgmin.empty
          (HashSelect.best BinaryArgmin.value (scored score seed)
            (rest.map (scored score))) []).withPC none) := by
  obtain ⟨n, hn, regs', _, ht⟩ := select_cons p mass frame score valid B C cost
    hmass seed rest regs hp
  exact ⟨n + 1, Nat.add_le_add_right hn 1, regs', compiled_halt_trace ht _ _⟩

/-- The machine's cached binary scores implement the pure strict argmin. -/
theorem best_scored (score : List Bool → List Bool) (seed : List Bool)
    (rest : List (List Bool)) :
    HashSelect.best BinaryArgmin.value (scored score seed) (rest.map (scored score)) =
      scored score (HashSelect.best (fun bits => BinaryArithmetic.toNat (score bits)) seed rest) := by
  induction rest generalizing seed with
  | nil => rfl
  | cons bits rest ih =>
    simp only [List.map_cons, HashSelect.best, scored, BinaryArgmin.value]
    by_cases h : BinaryArithmetic.toNat (score bits) < BinaryArithmetic.toNat (score seed)
    · simp only [h, ite_true]
      exact ih bits
    · simp only [h, ite_false]
      exact ih seed

/-- Every candidate, including every failed trial, contributes its callback
bound once. The extra term pays parsing, binary comparisons and queue control. -/
theorem selectBudget_callback (B C cost count : ℕ) :
    selectBudget B C cost count = (count + 1) * cost +
      (count + 1) * (6 * C + 100 * (B + C + 1) + 14) := by
  unfold selectBudget loadBudget
  ring

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
