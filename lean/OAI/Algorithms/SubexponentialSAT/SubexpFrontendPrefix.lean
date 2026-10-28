import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.FrontendProgram
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# A raw-input program for the growing parameters

The program has fixed control and six Boolean stacks. It parses the existing
canonical input, retains the declared count, computes both binary logarithms,
and divides their result by sixteen. The body remains on stack 0, while stacks
2, 4, and 5 hold n, s(n), and u(n). Stacks 1 and 3 are cleared work space.

This implementation uses the declared variable universe. The canonical unary
header already proves n <= input length, and the executable sparsifier performs
its own normalization. The separate dense-renaming semantics remain available
in SubexpFrontend; no unproved remapping program is called here.
-/

namespace SubexponentialSAT.SubexpFrontendPrefix

open BitProgram
open StructuredCalls

def storage (body nb sb ub : List Bool) (i : Fin 6) : List Bool :=
  if i = 0 then body else if i = 2 then nb else if i = 4 then sb
  else if i = 5 then ub else []

def state (body nb sb ub : List Bool) : State 3 6 :=
  ⟨fun _ => false, storage body nb sb ub⟩

def initPort : Fin 4 → Fin 6 := Fin.castAdd 2

def calcPort (dst : Fin 6) (i : Fin 3) : Fin 6 :=
  if i = 0 then dst else if i = 1 then 1 else 3

theorem initPort_injective : Function.Injective initPort := Fin.castAdd_injective 4 2

theorem calcPort_four_injective : Function.Injective (calcPort 4) := by decide

theorem calcPort_five_injective : Function.Injective (calcPort 5) := by decide

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

private theorem embed_eq {s : ℕ} (port : Fin s → Fin 6) (hinj : Function.Injective port)
    (frame : State 3 6) (small : State 3 s) (out : State 3 6)
    (hr : ∀ i, small.regs i = out.regs i)
    (hi : ∀ j, small.stacks j = out.stacks (port j))
    (ho : ∀ i, (¬ ∃ j, port j = i) → frame.stacks i = out.stacks i) :
    embedState id port frame small = out := by
  apply state_ext
  · funext i
    exact (embedState_register id port frame small Function.injective_id i).trans (hr i)
  · funext i
    by_cases h : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_stack id port frame small hinj j).trans (hi j)
    · exact (embedState_stack_frame id port frame small i h).trans (ho i h)

theorem embed_initial (input : List Bool) :
    embedState id initPort (state [] [] [] []) (StructuredProgram.ioState 0 input) =
      state input [] [] [] := by
  apply embed_eq _ initPort_injective
  · intro i
    rfl
  · intro j
    fin_cases j <;> simp [ initPort, state, storage]
  · intro i hi
    have h0 : i ≠ 0 := by
      intro h
      exact hi ⟨0, by simpa [initPort] using h.symm⟩
    simp [state, storage, h0]

theorem embed_initialized (body nb : List Bool) :
    embedState id initPort (state [] [] [] [])
      (StructuredProgram.State.ofCfg (FrontendProgram.cfg none false false body [] nb [])) =
      state body nb [] [] := by
  apply embed_eq _ initPort_injective
  · intro i
    fin_cases i <;> rfl
  · intro j
    fin_cases j <;> simp [StructuredProgram.State.ofCfg, FrontendProgram.cfg,
      FrontendProgram.storage, initPort, state, storage]
  · intro i hi
    have h0 : i ≠ 0 := by
      intro h
      exact hi ⟨0, by simpa [initPort] using h.symm⟩
    have h2 : i ≠ 2 := by
      intro h
      exact hi ⟨2, by simpa [initPort] using h.symm⟩
    simp [state, storage, h0, h2]

theorem embed_four (body nb ub word : List Bool) :
    embedState id (calcPort 4) (state body nb [] ub)
      (StructuredProgram.ioState 0 word) = state body nb word ub := by
  apply embed_eq _ calcPort_four_injective
  · intro i
    rfl
  · intro j
    fin_cases j <;> simp [ calcPort, state, storage]
  · intro i hi
    have h4 : i ≠ 4 := by
      intro h
      exact hi ⟨0, by simpa [calcPort] using h.symm⟩
    simp [state, storage, h4]

theorem embed_five (body nb sb word : List Bool) :
    embedState id (calcPort 5) (state body nb sb [])
      (StructuredProgram.ioState 0 word) = state body nb sb word := by
  apply embed_eq _ calcPort_five_injective
  · intro i
    rfl
  · intro j
    fin_cases j <;> simp [ calcPort, state, storage]
  · intro i hi
    have h5 : i ≠ 5 := by
      intro h
      exact hi ⟨0, by simpa [calcPort] using h.symm⟩
    simp [state, storage, h5]

abbrev initializeCmd : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram FrontendProgram.initializeProgram id initPort)

abbrev copyN : Cmd 3 6 := .call (StackRoutines.copyProgram 2 4 1 0 1)

abbrev computeS : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram SubexpParameterProgram.doubleLogProgram id (calcPort 4))

abbrev copyS : Cmd 3 6 := .call (StackRoutines.copyProgram 4 5 1 0 1)

abbrev computeU : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram SubexpParameterProgram.shiftFourProgram id (calcPort 5))

abbrev command : Cmd 3 6 := .seq initializeCmd (.seq copyN (.seq computeS (.seq copyS computeU)))

def program := StructuredCalls.compiled command 0 0

theorem initialize_eval (n : ℕ) (body : List Bool) :
    ∃ nb t, CounterPrograms.value nb = n ∧ nb.length ≤ n ∧
      t ≤ FrontendProgram.initializeBound n ∧
      Eval initializeCmd t (state (Encoding.encodeNat n ++ body) [] [] [])
        (state body nb [] []) := by
  obtain ⟨nb, hv, hl, t, ht, hrun⟩ := FrontendProgram.initialize_raw n body
  refine ⟨nb, t, hv, hl, ht, ?_⟩
  have h := eval_call_lifted FrontendProgram.initializeProgram id initPort
    (state [] [] [] []) Function.injective_id initPort_injective
    (a := StructuredProgram.ioState 0 (Encoding.encodeNat n ++ body))
    (b := StructuredProgram.State.ofCfg (FrontendProgram.cfg none false false body [] nb [])) hrun
  simpa only [initializeCmd, embed_initial, embed_initialized] using h

theorem computeS_eval (body nb ub word : List Bool) :
    ∃ sb t, CounterPrograms.value sb = SubexpPackingParameters.s (CounterPrograms.value word) ∧
      sb.length ≤ word.length ∧ t ≤ 2 * SubexpParameterProgram.logBound word.length ∧
      Eval computeS t (state body nb word ub) (state body nb sb ub) := by
  obtain ⟨sb, hv, hl, t, ht, hrun⟩ := SubexpParameterProgram.doubleLog_correct word
  refine ⟨sb, t, hv, hl, ht, ?_⟩
  have h := eval_call_lifted SubexpParameterProgram.doubleLogProgram id (calcPort 4)
    (state body nb [] ub) Function.injective_id calcPort_four_injective
    (a := StructuredProgram.ioState 0 word) (b := StructuredProgram.ioState 0 sb) hrun
  simpa only [computeS, embed_four] using h

theorem computeU_eval (body nb sb word : List Bool) :
    Eval computeU 7 (state body nb sb word) (state body nb sb (word.drop 4)) := by
  have h := eval_call_lifted SubexpParameterProgram.shiftFourProgram id (calcPort 5)
    (state body nb sb []) Function.injective_id calcPort_five_injective
    (a := StructuredProgram.ioState 0 word) (b := StructuredProgram.ioState 0 (word.drop 4))
    (SubexpParameterProgram.shiftFour_trace word)
  simpa only [computeU, embed_five] using h

private theorem readRegs_false :
    readRegs (fun _ : Fin 3 => false) 0 1 none = fun _ => false := by
  funext i
  fin_cases i <;> rfl

theorem copyN_eval (body nb : List Bool) :
    Eval copyN (7 * nb.length + 5) (state body nb [] []) (state body nb nb []) := by
  have hc := StackRoutines.copyProgram_trace (r := 3) (s := 6) 2 4 1 0 1
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (storage body nb [] []) rfl
  have ht := StackRoutines.halt_after_trace _ hc 7 rfl rfl
  have hs : StackRoutines.copyStacks 2 4 (storage body nb [] []) =
      storage body nb nb [] := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, storage]
  have hstorage : storage body nb [] [] 2 = nb := by
    simp [storage]
  rw [hstorage] at ht
  apply Eval.call
  simpa only [copyN, state, storage, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, StackRoutines.copyResult, readRegs_false, hs, Nat.add_assoc,
    Nat.reduceAdd] using ht

theorem copyS_eval (body nb sb : List Bool) :
    Eval copyS (7 * sb.length + 5) (state body nb sb []) (state body nb sb sb) := by
  have hc := StackRoutines.copyProgram_trace (r := 3) (s := 6) 4 5 1 0 1
    (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (storage body nb sb []) rfl
  have ht := StackRoutines.halt_after_trace _ hc 7 rfl rfl
  have hs : StackRoutines.copyStacks 4 5 (storage body nb sb []) =
      storage body nb sb sb := by
    funext i
    fin_cases i <;> simp [StackRoutines.copyStacks, storage]
  have hstorage : storage body nb sb [] 4 = sb := by
    simp [storage]
  rw [hstorage] at ht
  apply Eval.call
  simpa only [copyS, state, storage, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, StackRoutines.copyResult, readRegs_false, hs, Nat.add_assoc,
    Nat.reduceAdd] using ht

/-- Includes the outer halt and both preserving copies. -/
def bound (L : ℕ) : ℕ :=
  FrontendProgram.initializeBound L + 2 * SubexpParameterProgram.logBound L + 14 * L + 18

theorem bound_eq (L : ℕ) : bound L = 24 * L ^ 2 + 60 * L + 49 := by
  simp only [bound, FrontendProgram.initializeBound, SubexpParameterProgram.logBound]
  ring

theorem bound_mono {L M : ℕ} (h : L ≤ M) : bound L ≤ bound M := by
  unfold bound
  exact Nat.add_le_add_right
    (Nat.add_le_add
      (Nat.add_le_add (FrontendProgram.initializeBound_mono h)
        (Nat.mul_le_mul_left 2 (SubexpParameterProgram.logBound_mono h)))
      (Nat.mul_le_mul_left 14 h)) 18

theorem program_initial (input : List Bool) :
    (state input [] [] []).withPC (some program.entry) = initial program input := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- One fixed program computes all three retained integer words directly
from the raw unary-header input and preserves the entire formula body. -/
theorem run_raw (n : ℕ) (body : List Bool) :
    ∃ nb sb ub : List Bool,
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      nb.length ≤ n ∧ sb.length ≤ n ∧ ub.length ≤ n ∧
      RunsIn program (bound n) (initial program (Encoding.encodeNat n ++ body))
        ((state body nb sb ub).withPC none) := by
  obtain ⟨nb, t₀, hnb, hnl, ht₀, hinit⟩ := initialize_eval n body
  obtain ⟨sb, t₁, hsb, hsl, ht₁, hlog⟩ := computeS_eval body nb [] nb
  have hs : CounterPrograms.value sb = SubexpPackingParameters.s n := by simpa [hnb] using hsb
  have hu : CounterPrograms.value (sb.drop 4) = SubexpPackingParameters.u n := by
    rw [SubexpParameterProgram.shiftFour_value, hs]
    rfl
  have heval : Eval command
      (t₀ + ((7 * nb.length + 5) + (t₁ + ((7 * sb.length + 5) + 7))))
      (state (Encoding.encodeNat n ++ body) [] [] []) (state body nb sb (sb.drop 4)) :=
    Eval.seq hinit (Eval.seq (copyN_eval body nb)
      (Eval.seq hlog (Eval.seq (copyS_eval body nb sb) (computeU_eval body nb sb sb))))
  have htrace := StructuredCalls.compiled_halt_trace heval 0 0
  change Trace program _
    ((state (Encoding.encodeNat n ++ body) [] [] []).withPC (some program.entry)) _ at htrace
  rw [program_initial] at htrace
  have hlogbound := (Nat.mul_le_mul_left 2
    (SubexpParameterProgram.logBound_mono hnl))
  refine ⟨nb, sb, sb.drop 4, hnb, hs, hu, hnl, hsl.trans hnl, ?_, ?_⟩
  · exact (by simp : (sb.drop 4).length ≤ sb.length).trans (hsl.trans hnl)
  · refine ⟨_, ?_, htrace⟩
    unfold bound
    omega

/-- The actual canonical CNF input is accepted directly, with a fixed
quadratic source-step bound in its encoded length. -/
theorem run_formula {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ nb sb ub : List Bool,
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      nb.length ≤ n ∧ sb.length ≤ n ∧ ub.length ≤ n ∧
      RunsIn program (bound (Encoding.formulaBitLength F))
        (initial program (Encoding.encodeCNF F))
        ((state (Encoding.encodeCNFBody F) nb sb ub).withPC none) := by
  obtain ⟨nb, sb, ub, hn, hs, hu, hnl, hsl, hul, hr⟩ := run_raw n (Encoding.encodeCNFBody F)
  exact ⟨nb, sb, ub, hn, hs, hu, hnl, hsl, hul,
    hr.mono (bound_mono (Encoding.numVariables_le_formulaBitLength F))⟩

/-- The compiler turns this raw-input prefix into an actual primitive-tape
run. The multiplier is fixed by the single finite program, before n or F. -/
theorem run_formula_primitive {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ nb sb ub : List Bool,
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * bound (Encoding.formulaBitLength F))
        ((primitive program).init (Encoding.encodeCNF F))
        (primitiveCfg program ((state (Encoding.encodeCNFBody F) nb sb ub).withPC none)) := by
  obtain ⟨nb, sb, ub, hn, hs, hu, _, _, _, hr⟩ := run_formula F
  refine ⟨nb, sb, ub, hn, hs, hu, ?_⟩
  simpa only [primitive_initial] using BitProgram.primitive_execution program hr

end SubexponentialSAT.SubexpFrontendPrefix

end OAI.Algorithms
