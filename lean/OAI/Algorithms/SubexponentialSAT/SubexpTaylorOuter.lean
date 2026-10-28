import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorSweep
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorSemantics

namespace OAI.Algorithms

/-! Fixed outer source-coefficient control for polynomial shifting.  The
affine sweep occupies ports 0--86; port 87 retains the unprocessed source. -/

namespace SubexponentialSAT.SubexpTaylorOuter

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpTaylorControl

def outerState (regs : Fin 8 → Bool) (w : Words) (source : List Bool) : State 8 88 :=
  ⟨regs, Fin.addCases (m := 87) (n := 1) (store w) (fun _ => source)⟩

@[simp] theorem outerState_inner (regs : Fin 8 → Bool) (w : Words)
    (source : List Bool) (i : Fin 87) :
    (outerState regs w source).stacks (Fin.castAdd 1 i) = store w i := by
  simp [outerState]

@[simp] theorem outerState_source (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 87 = source := rfl

@[simp] theorem outerState_80 (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 80 = w.coefficient := rfl
@[simp] theorem outerState_81 (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 81 = w.blockWidth := rfl
@[simp] theorem outerState_82 (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 82 = w.index := rfl
@[simp] theorem outerState_83 (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 83 = w.scratch := rfl
@[simp] theorem outerState_84 (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 84 = [] := rfl
@[simp] theorem outerState_85 (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    (outerState regs w source).stacks 85 = [] := rfl

@[simp] theorem inner_ne_source (i : Fin 87) :
    (Fin.castAdd 1 i : Fin 88) ≠ 87 := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
  omega

@[simp] theorem inner_eq_coefficient (i : Fin 87) :
    (Fin.castAdd 1 i : Fin 88) = 80 ↔ i = 80 := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun j : Fin 88 => j.val) h
  · intro h
    subst i
    rfl

theorem outer_ext {a b : State 8 88} (hr : a.regs = b.regs)
    (hi : ∀ i : Fin 87, a.stacks (Fin.castAdd 1 i) = b.stacks (Fin.castAdd 1 i))
    (hs : a.stacks 87 = b.stacks 87) : a = b := by
  apply state_ext hr
  funext i
  refine Fin.addCases (m := 87) (n := 1) ?_ ?_ i
  · exact hi
  · intro j
    fin_cases j
    exact hs

def innerPorts : Fin 87 ↪ Fin 88 := ⟨Fin.castAdd 1, Fin.castAdd_injective _ _⟩

theorem embed_inner (frameRegs regs : Fin 8 → Bool) (frameWords w : Words)
    (source : List Bool) :
    embedState id innerPorts (outerState frameRegs frameWords source) (state regs w) =
      outerState regs w source := by
  apply embedState_eq _ _ Function.injective_id innerPorts.injective
  · intro i; rfl
  · intro i; simp [innerPorts, state]
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    have h87 : i = 87 := by
      apply Fin.ext
      by_contra h
      have hil : i.val < 87 := by have := i.isLt; omega
      exact hi ⟨⟨i.val, hil⟩, by apply Fin.ext; rfl⟩
    subst i
    rfl

abbrev callSweep {l : ℕ} (sweepProgram : Program 8 87 l) : Cmd 8 88 :=
  .call (ProgramLinking.liftProgram sweepProgram id innerPorts)

theorem callSweep_eval {l n : ℕ} (sweepProgram : Program 8 87 l)
    (regs regs' : Fin 8 → Bool) (w w' : Words) (source : List Bool)
    (h : Trace sweepProgram n ((state regs w).withPC (some sweepProgram.entry))
      ((state regs' w').withPC none)) :
    Eval (callSweep sweepProgram) n (outerState regs w source) (outerState regs' w' source) := by
  have he := eval_call_lifted sweepProgram id innerPorts (outerState regs w source)
    Function.injective_id innerPorts.injective h
  simpa only [callSweep, embed_inner] using he

abbrev takeSource : Cmd 8 88 :=
  .seq (takeWord 81 82 83 87 80 0 1)
    (.call (StackRoutines.reverseProgram 80 84 85 (0 : Fin 8) 1))

theorem takeSource_eval (regs : Fin 8 → Bool) (w : Words) (bits rest : List Bool)
    (hw : w.blockWidth.length = bits.length) (hc : w.coefficient = [])
    (hi : w.index = []) (ht : w.scratch = []) :
    Eval takeSource (23 * bits.length + 18)
      (outerState regs w (bits.reverse ++ rest))
      (outerState (readRegs regs 0 1 none) {w with coefficient := bits} rest) := by
  let a := outerState regs w (bits.reverse ++ rest)
  let mid := outerState (readRegs regs 0 1 none) {w with coefficient := bits.reverse} rest
  have h1 := takeWord_eval a 81 82 83 87 80 0 1 (by decide) (by decide) bits.reverse rest
    rfl (by simp [a, hi]) (by simp [a, ht])
    (by simpa [a] using hw)
  have e1 : afterTake a 87 80 0 1 bits.reverse rest = mid := by
    apply outer_ext
    · rfl
    · intro i
      by_cases h80 : i = 80 <;> simp [afterTake, a, mid, store, hc, h80]
    · simp [afterTake, a, mid]
  rw [e1] at h1
  have h2 := reverse_eval mid 80 84 85 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [mid]) (by simp [mid])
  have e2 : afterReverse mid 80 0 1 =
      outerState (readRegs regs 0 1 none) {w with coefficient := bits} rest := by
    apply outer_ext
    · simp [afterReverse, mid, outerState, StackRoutines.readRegs_reset]
    · intro i
      by_cases h80 : i = 80 <;>
        simp [afterReverse, StackRoutines.reverseStacks, mid, store, h80]
    · simp [afterReverse, StackRoutines.reverseStacks, mid]
  rw [e2] at h2
  convert h1.seq h2 using 1
  simp [mid]
  omega

abbrev reverseSource : Cmd 8 88 := .call (StackRoutines.reverseProgram 87 84 85 (0 : Fin 8) 1)

theorem reverseSource_eval (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    Eval reverseSource (9 * source.length + 7) (outerState regs w source)
      (outerState (readRegs regs 0 1 none) w source.reverse) := by
  have h := reverse_eval (outerState regs w source) 87 84 85 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp)
  have hsource : (outerState regs w source).stacks 87 = source := by
    rfl
  rw [hsource] at h
  convert h using 1
  apply outer_ext
  · rfl
  · intro i
    simp [afterReverse, StackRoutines.reverseStacks]
  · simp [afterReverse, StackRoutines.reverseStacks]

abbrev guard : Cmd 8 88 := .base (.atom (.peek 87 0 1))
abbrev iteration {l : ℕ} (sweepProgram : Program 8 87 l) : Cmd 8 88 :=
  .seq takeSource (callSweep sweepProgram)
abbrev loop {l : ℕ} (sweepProgram : Program 8 87 l) : Cmd 8 88 :=
  .while 1 (.seq (iteration sweepProgram) guard)
abbrev command {l : ℕ} (sweepProgram : Program 8 87 l) : Cmd 8 88 :=
  .seq reverseSource (.seq guard (loop sweepProgram))
abbrev reversedCommand {l : ℕ} (sweepProgram : Program 8 87 l) : Cmd 8 88 :=
  .seq guard (loop sweepProgram)
abbrev program {l : ℕ} (sweepProgram : Program 8 87 l) :
    Program 8 88 (size (command sweepProgram) + 1) := compiled (command sweepProgram) 87 77
abbrev reversedProgram {l : ℕ} (sweepProgram : Program 8 87 l) :
    Program 8 88 (size (reversedCommand sweepProgram) + 1) :=
  compiled (reversedCommand sweepProgram) 87 77

theorem guard_eval (regs : Fin 8 → Bool) (w : Words) (source : List Bool) :
    Eval guard 1 (outerState regs w source)
      (outerState (readRegs regs 0 1 source.head?) w source) := by
  exact .base (.atom _ _)

def process {C : Type*} (step : C → C → C) : List C → List C → List C
  | [], Q => Q
  | b :: bs, Q => process step bs (sweep step b Q)

theorem process_append {C : Type*} (step : C → C → C) (bs cs Q : List C) :
    process step (bs ++ cs) Q = process step cs (process step bs Q) := by
  induction bs generalizing Q with
  | nil => rfl
  | cons b bs ih => simp [process, ih]

theorem process_reverse {C : Type*} (step : C → C → C) (P : List C) :
    process step P.reverse [] = SubexpTaylorSemantics.compactShift step P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp [List.reverse_cons, process_append, process, ih,
      SubexpTaylorSemantics.compactShift]

section Service

variable {C : Type*} (encode : C → List Bool) (B : ℕ)
  (hencode : ∀ a, (encode a).length = B) (hB : 0 < B)
  (base : Words) (hwidth : base.blockWidth.length = B)
  {labels : ℕ} (service : Program 8 87 labels) (step : C → C → C) (K : ℕ)
  (hservice : ∀ regs Q b,
    ∃ n ≤ Q.length * (K + 33 * B + 27) + 6 * B + 9, ∃ regs',
      Trace service n
        ((state regs (ready encode base Q b [])).withPC (some service.entry))
        ((state regs' (done base (encodeList encode (sweep step b Q)))).withPC none))

include hencode hwidth hservice

theorem iteration_eval (regs : Fin 8 → Bool) (b : C) (bs Q : List C) :
    ∃ n ≤ (Q.length + 1) * (K + 33 * B + 27), ∃ regs',
      Eval (iteration service) n
        (outerState regs (done base (encodeList encode Q)) (backward encode (b :: bs)))
        (outerState regs' (done base (encodeList encode (sweep step b Q))) (backward encode bs)) := by
  have ht := takeSource_eval regs (done base (encodeList encode Q)) (encode b)
    (backward encode bs) (by simpa [done] using hwidth.trans (hencode b).symm) rfl rfl rfl
  obtain ⟨n, hn, rr, hs⟩ := hservice (readRegs regs 0 1 none) Q b
  have hc := callSweep_eval service (readRegs regs 0 1 none) rr
    (ready encode base Q b []) (done base (encodeList encode (sweep step b Q)))
    (backward encode bs) hs
  refine ⟨23 * (encode b).length + 18 + n, ?_, rr, ?_⟩
  · rw [hencode]
    nlinarith
  · simpa only [iteration, done, ready, backward, List.flatMap_cons]
      using ht.seq hc

include hB

theorem loop_eval (N : ℕ) (regs : Fin 8 → Bool) (bs Q : List C)
    (hsize : Q.length + bs.length ≤ N) :
    ∃ n ≤ bs.length * ((N + 1) * (K + 33 * B + 27) + 2) + 1, ∃ regs',
      Eval (loop service) n
        (outerState (readRegs regs 0 1 (backward encode bs).head?)
          (done base (encodeList encode Q)) (backward encode bs))
        (outerState regs' (done base (encodeList encode (process step bs Q))) []) := by
  induction bs generalizing Q regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
      exact Eval.while_false (by simp [outerState, readRegs, backward])
  | cons b bs ih =>
      obtain ⟨ni, hni, ri, hi⟩ := iteration_eval encode B hencode base hwidth service step K
        hservice (readRegs regs 0 1 (backward encode (b :: bs)).head?) b bs Q
      have hg := guard_eval ri (done base (encodeList encode (sweep step b Q))) (backward encode bs)
      have hsize' : (sweep step b Q).length + bs.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize
      obtain ⟨nr, hnr, rr, hr⟩ := ih ri (sweep step b Q) hsize'
      have htest :
          (outerState (readRegs regs 0 1 (backward encode (b :: bs)).head?)
            (done base (encodeList encode Q)) (backward encode (b :: bs))).regs 1 = true := by
        have hb : encode b ≠ [] := by
          intro h
          have hl := congrArg List.length h
          simp [hencode] at hl
          omega
        simp [outerState, readRegs, backward, List.head?_append, hb]
      refine ⟨ni + 1 + nr + 1, ?_, rr, ?_⟩
      · have hq : Q.length + 1 ≤ N + 1 := by simp only [List.length_cons] at hsize; omega
        have hi' := hni.trans (Nat.mul_le_mul_right (K + 33 * B + 27) hq)
        let A := (N + 1) * (K + 33 * B + 27)
        change ni ≤ A at hi'
        change ni + 1 + nr + 1 ≤ (bs.length + 1) * (A + 2) + 1
        have hbound : (bs.length + 1) * (A + 2) + 1 =
            bs.length * (A + 2) + 1 + A + 2 := by ring
        rw [hbound]
        change nr ≤ bs.length * (A + 2) + 1 at hnr
        omega
      · simpa only [loop, process, Nat.add_assoc] using Eval.while_true htest (hi.seq hg) hr

omit hB hwidth hservice in
theorem encodeList_length (xs : List C) : (encodeList encode xs).length = xs.length * B := by
  induction xs with
  | nil => simp [encodeList]
  | cons a xs ih => simp [encodeList, hencode, Nat.add_mul, Nat.add_comm]

omit hencode hB hwidth hservice in
theorem encodeList_reverse (xs : List C) :
    (encodeList encode xs).reverse = backward encode xs.reverse := by
  simpa only [encodeList, backward, Function.comp_def] using
    (List.reverse_flatMap (l := xs) (f := encode))

theorem command_eval (regs : Fin 8 → Bool) (P : List C) :
    ∃ n ≤ 9 * (P.length * B) +
      P.length * ((P.length + 1) * (K + 33 * B + 27) + 2) + 9, ∃ regs',
      Eval (command service) n
        (outerState regs (done base []) (encodeList encode P))
        (outerState regs' (done base
          (encodeList encode (SubexpTaylorSemantics.compactShift step P))) []) := by
  have hr := reverseSource_eval regs (done base []) (encodeList encode P)
  rw [encodeList_reverse encode P] at hr
  have hg := guard_eval (readRegs regs 0 1 none) (done base []) (backward encode P.reverse)
  obtain ⟨n, hn, rr, hl⟩ := loop_eval encode B hencode hB base hwidth service step K hservice
    P.length (readRegs regs 0 1 none) P.reverse [] (by simp)
  refine ⟨9 * (encodeList encode P).length + 7 + (1 + n), ?_, rr, ?_⟩
  · rw [encodeList_length encode B hencode]
    simp only [List.length_reverse] at hn
    omega
  · simpa only [command, encodeList, List.flatMap_nil, process_reverse] using hr.seq (hg.seq hl)

theorem program_trace (regs : Fin 8 → Bool) (P : List C) :
    ∃ n ≤ 9 * (P.length * B) +
      P.length * ((P.length + 1) * (K + 33 * B + 27) + 2) + 10, ∃ regs',
      Trace (program service) n
        ((outerState regs (done base []) (encodeList encode P)).withPC
          (some (program service).entry))
        ((outerState regs' (done base
          (encodeList encode (SubexpTaylorSemantics.compactShift step P))) []).withPC none) := by
  obtain ⟨n, hn, rr, hr⟩ := command_eval encode B hencode hB base hwidth service step K
    hservice regs P
  exact ⟨n + 1, by omega, rr, compiled_halt_trace hr 87 77⟩

/-- Record parsers already return reversed payload bytes. This entry point
consumes that representation directly, without two extra row reversals. -/
theorem reversed_program_trace (regs : Fin 8 → Bool) (P : List C) :
    ∃ n ≤ P.length * ((P.length + 1) * (K + 33 * B + 27) + 2) + 3, ∃ regs',
      Trace (reversedProgram service) n
        ((outerState regs (done base []) (encodeList encode P).reverse).withPC
          (some (reversedProgram service).entry))
        ((outerState regs' (done base
          (encodeList encode (SubexpTaylorSemantics.compactShift step P))) []).withPC none) := by
  have hg := guard_eval regs (done base []) (backward encode P.reverse)
  obtain ⟨n, hn, rr, hl⟩ := loop_eval encode B hencode hB base hwidth service step K hservice
    P.length regs P.reverse [] (by simp)
  have he : Eval (reversedCommand service) (1 + n)
      (outerState regs (done base []) (encodeList encode P).reverse)
      (outerState rr (done base
        (encodeList encode (SubexpTaylorSemantics.compactShift step P))) []) := by
    rw [encodeList_reverse encode P]
    simpa only [reversedCommand, encodeList,
      List.flatMap_nil, process_reverse] using hg.seq hl
  refine ⟨(1 + n) + 1, ?_, rr, compiled_halt_trace he 87 77⟩
  simp only [List.length_reverse] at hn
  omega

end Service

end SubexponentialSAT.SubexpTaylorOuter

end OAI.Algorithms
