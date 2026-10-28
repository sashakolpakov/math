import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking

namespace OAI.Algorithms

/-!
# Preserving preparation of a local field-label row

Copy the enumerator's rank and the factor's unary arity into the checked
unranking routine, produce the fixed-width digit stream, and clear the padded
final quotient. The modulus, rank master, and arity master are preserved.
-/

namespace SubexponentialSAT.SubexpFieldRowPreparation

open BitProgram StructuredCalls StackRoutines

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

/-- The unranking workspace occupies ports 0--12. Ports 13 and 14 are masters. -/
def tapes (modulus rankMaster arityMaster rank arity output : List Bool) : Fin 15 → List Bool :=
  fun i => if i = 5 then modulus else if i = 6 then rank else if i = 8 then arity
    else if i = 12 then output else if i = 13 then rankMaster
    else if i = 14 then arityMaster else []

def data (regs : Fin 8 → Bool)
    (modulus rankMaster arityMaster rank arity output : List Bool) : State 8 15 :=
  ⟨regs, tapes modulus rankMaster arityMaster rank arity output⟩

@[simp] theorem tapes_5 (m rm am r a o : List Bool) : tapes m rm am r a o 5 = m := rfl
@[simp] theorem tapes_6 (m rm am r a o : List Bool) : tapes m rm am r a o 6 = r := rfl
@[simp] theorem tapes_8 (m rm am r a o : List Bool) : tapes m rm am r a o 8 = a := rfl
@[simp] theorem tapes_10 (m rm am r a o : List Bool) : tapes m rm am r a o 10 = [] := rfl
@[simp] theorem tapes_12 (m rm am r a o : List Bool) : tapes m rm am r a o 12 = o := rfl
@[simp] theorem tapes_13 (m rm am r a o : List Bool) : tapes m rm am r a o 13 = rm := rfl
@[simp] theorem tapes_14 (m rm am r a o : List Bool) : tapes m rm am r a o 14 = am := rfl

@[simp] theorem tapes_update_6 (m rm am r a o word : List Bool) :
    Function.update (tapes m rm am r a o) 6 word = tapes m rm am word a o := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem tapes_update_8 (m rm am r a o word : List Bool) :
    Function.update (tapes m rm am r a o) 8 word = tapes m rm am r word o := by
  funext i; fin_cases i <;> simp [tapes]

def stackPort (i : Fin 13) : Fin 15 := i.castLE (by decide)

theorem stackPort_injective : Function.Injective stackPort := by
  intro i j h
  apply Fin.ext
  simpa [stackPort] using congrArg (fun x : Fin 15 => x.val) h

private theorem embed_unrank (regs oldRegs : Fin 8 → Bool)
    (m rm am x ar out oldX oldAr oldOut : List Bool) :
    embedState id stackPort (data oldRegs m rm am oldX oldAr oldOut)
      (SubexpBasePUnranking.state regs m x ar [] out) = data regs m rm am x ar out := by
  apply state_ext
  · exact ProgramLinking.extend_id _ _
  · funext j
    by_cases hj : j.val < 13
    · let k : Fin 13 := ⟨j.val, hj⟩
      have hk : stackPort k = j := Fin.ext rfl
      rw [← hk, embedState_stack id stackPort _ _ stackPort_injective]
      have hports : ∀ i : Fin 13,
          (SubexpBasePUnranking.state regs m x ar [] out).stacks i =
            (data regs m rm am x ar out).stacks (stackPort i) := by
        intro i
        fin_cases i <;> rfl
      exact hports k
    · have hout : ¬ ∃ k, stackPort k = j := by
        rintro ⟨k, hk⟩
        have hval := congrArg (fun i : Fin 15 => i.val) hk
        have hklt := k.isLt
        change k.val = j.val at hval
        omega
      rw [embedState_stack_frame id stackPort _ _ j hout]
      have hc : j = 13 ∨ j = 14 := by
        have hjlt := j.isLt
        have hv : j.val = 13 ∨ j.val = 14 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hc with rfl | rfl <;> rfl

abbrev unrank : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram SubexpBasePUnranking.program id stackPort)

theorem unrank_eval (regs : Fin 8 → Bool) (m rm am rank arity output : List Bool) :
    ∃ n ≤ SubexpBasePUnranking.budget m rank arity, ∃ finalRegs,
      Eval unrank n (data regs m rm am rank arity output)
        (data finalRegs m rm am
          (SubexpBasePUnranking.remainingRank m arity.length rank) []
          ((SubexpBasePUnranking.digitWords m arity.length rank).flatten ++ output)) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpBasePUnranking.program_runsIn regs m rank arity output
  have he := eval_call_lifted SubexpBasePUnranking.program id stackPort
    (data regs m rm am rank arity output) Function.injective_id stackPort_injective ht
  rw [embed_unrank, embed_unrank] at he
  exact ⟨n, hn, rf, he⟩

private theorem copy_eval (src dst : Fin 15) (hsd : src ≠ dst)
    (hst : src ≠ 10) (htd : (10 : Fin 15) ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 15 → List Bool) (ht : stk 10 = []) :
    Eval (.call (copyProgram src dst 10 (1 : Fin 8) 3)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst 10 (1 : Fin 8) 3 hsd hst htd (by decide) regs stk ht)
    7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using h

private theorem clear_eval (regs : Fin 8 → Bool) (stk : Fin 15 → List Bool) :
    Eval (.call (clearProgram 6 (1 : Fin 8) 3)) (2 * (stk 6).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, clearStacks 6 stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace (6 : Fin 15) (1 : Fin 8) 3 regs stk) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc] using h

abbrev command : Cmd 8 15 :=
  .seq (.call (copyProgram 13 6 10 1 3))
    (.seq (.call (copyProgram 14 8 10 1 3))
      (.seq unrank (.call (clearProgram 6 1 3))))

def budget (modulus rank arity : List Bool) : ℕ :=
  SubexpBasePUnranking.budget modulus rank arity + 9 * rank.length + 7 * arity.length + 13

/-- The local row label stream is built without changing either enumeration
master. The padded final quotient is actually cleared, even when its value is zero. -/
theorem command_eval (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ n ≤ budget modulus rank arity, ∃ finalRegs,
      Eval command n (data regs modulus rank arity [] [] output)
        (data finalRegs modulus rank arity [] []
          ((SubexpBasePUnranking.digitWords modulus arity.length rank).flatten ++ output)) := by
  have h₁ := copy_eval 13 6 (by decide) (by decide) (by decide) regs
    (tapes modulus rank arity [] [] output) rfl
  simp only [copyStacks, tapes_13, tapes_6, List.append_nil, tapes_update_6] at h₁
  have h₂ := copy_eval 14 8 (by decide) (by decide) (by decide) (readRegs regs 1 3 none)
    (tapes modulus rank arity rank [] output) rfl
  simp only [copyStacks, tapes_14, tapes_8, List.append_nil, tapes_update_8, readRegs_reset] at h₂
  obtain ⟨nu, hnu, rf, hu⟩ := unrank_eval (readRegs regs 1 3 none)
    modulus rank arity rank arity output
  have h₃ := clear_eval rf
    (tapes modulus rank arity (SubexpBasePUnranking.remainingRank modulus arity.length rank) []
      ((SubexpBasePUnranking.digitWords modulus arity.length rank).flatten ++ output))
  simp only [clearStacks, tapes_6, tapes_update_6, SubexpBasePUnranking.remainingRank_length] at h₃
  have h := h₁.seq (h₂.seq (hu.seq h₃))
  refine ⟨_, ?_, readRegs rf 1 3 none, h⟩
  dsimp [budget]
  omega

abbrev program : Program 8 15 (size command + 1) := compiled command 13 12

theorem program_runsIn (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ finalRegs,
      RunsIn program (budget modulus rank arity + 1)
        ((data regs modulus rank arity [] [] output).withPC (some program.entry))
        ((data finalRegs modulus rank arity [] []
          ((SubexpBasePUnranking.digitWords modulus arity.length rank).flatten ++ output)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval regs modulus rank arity output
  exact ⟨rf, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 13 12⟩

theorem control_size : size command + 1 = 144 := rfl

theorem program_primitive (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ finalRegs,
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * (budget modulus rank arity + 1))
        (BitProgram.primitiveCfg program
          ((data regs modulus rank arity [] [] output).withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((data finalRegs modulus rank arity [] []
            ((SubexpBasePUnranking.digitWords modulus arity.length rank).flatten ++ output)).withPC none)) := by
  obtain ⟨rf, hr⟩ := program_runsIn regs modulus rank arity output
  exact ⟨rf, BitProgram.primitive_execution program hr⟩

end SubexponentialSAT.SubexpFieldRowPreparation

end OAI.Algorithms
