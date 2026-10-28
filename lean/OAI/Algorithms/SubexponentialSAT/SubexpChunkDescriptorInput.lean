import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpChunkDescriptorProgram

namespace OAI.Algorithms

/-! Actual binary-to-unary entry path for the chunk descriptor producer. -/

namespace SubexponentialSAT.SubexpChunkDescriptorInput

open BitProgram StructuredProgram StructuredCalls
open SubexpChunkDescriptorProgram

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a
  · exact Function.extend_apply' _ _ _ h

abbrev conversion (ports : Fin 3 → Fin 10) : StructuredCalls.Cmd 3 10 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram id ports)

abbrev converted (ports : Fin 3 → Fin 10) (d : Data) : Data :=
  ⟨CounterConversions.zeroRegs,
    Function.update (Function.update (Function.update d.stacks (ports 0) [])
      (ports 1) (List.replicate (CounterPrograms.value (d.stacks (ports 0))) true ++ d.stacks (ports 1)))
      (ports 2) []⟩

theorem conversion_eval (ports : Fin 3 → Fin 10) (hp : Function.Injective ports)
    (d : Data) (hs : d.stacks (ports 2) = []) :
    ∃ n, StructuredCalls.Eval (conversion ports) n d (converted ports d) ∧
      n ≤ CounterConversions.runtimeBound (d.stacks (ports 0)) := by
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs d.regs
    (d.stacks (ports 0)) (d.stacks (ports 1))
  have he := StructuredCalls.eval_call_lifted CounterConversions.unaryProgram id ports d
    Function.injective_id hp ht
  have hbefore : StructuredCalls.embedState id ports d
      (CounterConversions.state d.regs (d.stacks (ports 0)) (d.stacks (ports 1))) = d := by
    apply CounterForPrograms.data_ext
    · change Function.extend id d.regs d.regs = d.regs
      exact extend_restrict_eq id d.regs
    · have hst : (CounterConversions.state d.regs (d.stacks (ports 0))
          (d.stacks (ports 1))).stacks = d.stacks ∘ ports := by
        funext i
        fin_cases i <;> simp [CounterConversions.state, hs]
      change Function.extend ports _ d.stacks = d.stacks
      rw [hst, extend_restrict_eq]
  have hafter : StructuredCalls.embedState id ports d
      (CounterConversions.state CounterConversions.zeroRegs []
        (List.replicate (CounterPrograms.value (d.stacks (ports 0))) true ++ d.stacks (ports 1))) =
      converted ports d := by
    apply CounterForPrograms.data_ext
    · funext i
      exact StructuredCalls.embedState_register id ports d _ Function.injective_id i
    · funext i
      have h01 : ports 0 ≠ ports 1 := hp.ne (by decide)
      have h02 : ports 0 ≠ ports 2 := hp.ne (by decide)
      have h12 : ports 1 ≠ ports 2 := hp.ne (by decide)
      by_cases h0 : i = ports 0
      · subst i
        rw [StructuredCalls.embedState_stack id ports d _ hp 0]
        simp [ CounterConversions.state, h01, h02 ]
      by_cases h1 : i = ports 1
      · subst i
        rw [StructuredCalls.embedState_stack id ports d _ hp 1]
        simp [ CounterConversions.state, h12 ]
      by_cases h2 : i = ports 2
      · subst i
        rw [StructuredCalls.embedState_stack id ports d _ hp 2]
        simp [ CounterConversions.state]
      · rw [StructuredCalls.embedState_stack_frame id ports d _ i (by
          rintro ⟨j, hj⟩
          fin_cases j <;> simp_all)]
        simp [ h0, h1, h2]
  exact ⟨n, by simpa [conversion, hbefore, hafter] using he, hn⟩

def nPorts : Fin 3 → Fin 10 := ![0, 4, 3]
def ellPorts : Fin 3 → Fin 10 := ![1, 2, 3]

abbrev adapterState (regs : Regs) (nBits ellBits unaryN unaryEll : List Bool) : Data :=
  ⟨regs, ![nBits, ellBits, unaryEll, [], unaryN, [], [], [], [], []]⟩

theorem convert_n (regs : Regs) (nBits ellBits : List Bool) :
    ∃ n, StructuredCalls.Eval (conversion nPorts) n
      (adapterState regs nBits ellBits [] [])
      (adapterState CounterConversions.zeroRegs [] ellBits
        (List.replicate (CounterPrograms.value nBits) true) []) ∧
      n ≤ CounterConversions.runtimeBound nBits := by
  obtain ⟨n, he, hn⟩ := conversion_eval nPorts (by decide)
    (adapterState regs nBits ellBits [] []) rfl
  refine ⟨n, ?_, hn⟩
  convert he using 1
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [ nPorts ]

theorem convert_ell (ellBits unaryN : List Bool) :
    ∃ n, StructuredCalls.Eval (conversion ellPorts) n
      (adapterState CounterConversions.zeroRegs [] ellBits unaryN [])
      (adapterState CounterConversions.zeroRegs [] [] unaryN
        (List.replicate (CounterPrograms.value ellBits) true)) ∧
      n ≤ CounterConversions.runtimeBound ellBits := by
  obtain ⟨n, he, hn⟩ := conversion_eval ellPorts (by decide)
    (adapterState CounterConversions.zeroRegs [] ellBits unaryN []) rfl
  refine ⟨n, ?_, hn⟩
  convert he using 1
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [ ellPorts ]

abbrev move (src dst : Fin 10) : StructuredCalls.Cmd 3 10 :=
  .call (StackRoutines.transferProgram src dst 0 1)

abbrev moved (src dst : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem move_eval (src dst : Fin 10) (h : src ≠ dst) (d : Data) :
    StructuredCalls.Eval (move src dst) (3 * (d.stacks src).length + 3) d (moved src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 h (by decide) d.regs d.stacks)

abbrev command : StructuredCalls.Cmd 3 10 :=
  .seq (conversion nPorts) (.seq (conversion ellPorts) (.seq (move 4 0) (move 2 1)))

def runtimeBound (nBits ellBits : List Bool) : ℕ :=
  CounterConversions.runtimeBound nBits + CounterConversions.runtimeBound ellBits +
    3 * (CounterPrograms.value nBits + CounterPrograms.value ellBits) + 6

theorem input_execution (regs : Regs) (nBits ellBits : List Bool) :
    ∃ n regs', StructuredCalls.Eval command n (work regs nBits ellBits [] [] [] [])
      (work regs' (List.replicate (CounterPrograms.value nBits) true)
        (List.replicate (CounterPrograms.value ellBits) true) [] [] [] []) ∧
      n ≤ runtimeBound nBits ellBits := by
  obtain ⟨n₁, h₁, hn₁⟩ := convert_n regs nBits ellBits
  obtain ⟨n₂, h₂, hn₂⟩ := convert_ell ellBits (List.replicate (CounterPrograms.value nBits) true)
  let d := adapterState CounterConversions.zeroRegs [] []
    (List.replicate (CounterPrograms.value nBits) true)
    (List.replicate (CounterPrograms.value ellBits) true)
  have h₃ := move_eval 4 0 (by decide) d
  have h₄ := move_eval 2 1 (by decide) (moved 4 0 d)
  refine ⟨n₁ + (n₂ + ((3 * CounterPrograms.value nBits + 3) +
    (3 * CounterPrograms.value ellBits + 3))), (moved 2 1 (moved 4 0 d)).regs, ?_, ?_⟩
  · have he := h₁.seq (h₂.seq (h₃.seq h₄))
    convert he using 1
    · simp [d, StackRoutines.transferStacks]
    · apply CounterForPrograms.data_ext
      · rfl
      · funext i
        fin_cases i <;> simp [ work  ]
    · apply CounterForPrograms.data_ext
      · rfl
      · funext i
        fin_cases i <;> simp [d, work, StackRoutines.transferStacks]
  · dsimp [runtimeBound]
    omega

end SubexponentialSAT.SubexpChunkDescriptorInput

end OAI.Algorithms
