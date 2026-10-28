import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- The tuple remains on837 and its past-the-end head address remains on845.
The visitor borrows840 and843, which are empty at a complete tuple. -/
def setup : Code :=
  .seq (copyWord 837 840 841) (copyWord 845 843 841)

noncomputable def setupState (a : Data) : Data :=
  copyState 845 843 (copyState 837 840 a)

theorem setup_eval (a : Data) (htmp : a.stacks 841 = []) :
    Eval setup (7 * (a.stacks 837).length + 7 * (a.stacks 845).length + 10)
      a (setupState a) := by
  have h1 := copyWord_eval 837 840 841 (by decide) (by decide) (by decide) a htmp
  have ht : (copyState 837 840 a).stacks 841 = [] := by
    simpa [copyState, StackRoutines.copyStacks] using htmp
  have h2 := copyWord_eval 845 843 841 (by decide) (by decide) (by decide)
    (copyState 837 840 a) ht
  have he := h1.seq h2
  have h845 : (copyState 837 840 a).stacks 845 = a.stacks 845 := by
    simp [copyState, StackRoutines.copyStacks]
  simpa only [setup, setupState, h845, show
    7 * (a.stacks 837).length + 5 + (7 * (a.stacks 845).length + 5) =
      7 * (a.stacks 837).length + 7 * (a.stacks 845).length + 10 by omega] using he

theorem setupState_words (a : Data) (h840 : a.stacks 840 = []) (h843 : a.stacks 843 = []) :
    (setupState a).stacks 840 = a.stacks 837 ∧
      (setupState a).stacks 843 = a.stacks 845 := by
  simp [setupState, copyState, StackRoutines.copyStacks, h840, h843]

theorem setupState_frame (a : Data) (i : Fin 896) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (setupState a).stacks i = a.stacks i := by
  simp [setupState, copyState, StackRoutines.copyStacks, h840, h843]

/-- Parsing restores the original little-endian representative, including
zero-width heads. The address pop is justified by its nonempty input below. -/
def readHead : Code :=
  .seq (popWordCommand 840 838 (by decide)) (.base (.atom (.pop 843 0 1)))

noncomputable def headState (a : Data) (word tail address : List Bool) : Data :=
  let b := popWordState 840 838 (by decide) a word tail
  ⟨readRegs b.regs 0 1 (some true), Function.update b.stacks 843 address⟩

theorem readHead_eval (a : Data) (word tail address : List Bool)
    (hframes : a.stacks 840 = Encoding.frame word.reverse ++ tail)
    (hword : a.stacks 838 = []) (haddress : a.stacks 843 = true :: address) :
    Eval readHead (6 * word.length + 5) a (headState a word tail address) := by
  have hp := popWord_eval 840 838 (by decide) a word tail hframes hword
  let b := popWordState 840 838 (by decide) a word tail
  have hb : b.stacks 843 = true :: address := by
    rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide)]
    exact haddress
  have he : Eval (.base (.atom (.pop 843 0 1))) 1 b (headState a word tail address) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop 843 0 1) b) using 1
    apply SubexpScanPrimitives.state_ext
    · change readRegs b.regs 0 1 (some true) = readRegs b.regs 0 1 (b.stacks 843).head?
      rw [hb]
      rfl
    · change Function.update b.stacks 843 address = Function.update b.stacks 843 (b.stacks 843).tail
      rw [hb]
      rfl
  simpa only [readHead, headState,
    show 6 * word.length + 4 + 1 = 6 * word.length + 5 by omega] using hp.seq he

theorem headState_words (a : Data) (word tail address : List Bool) :
    (headState a word tail address).stacks 838 = word ∧
      (headState a word tail address).stacks 840 = tail ∧
      (headState a word tail address).stacks 843 = address := by
  simp only [headState, Function.update_of_ne (by decide : (838 : Fin 896) ≠ 843),
    Function.update_of_ne (by decide : (840 : Fin 896) ≠ 843), Function.update_self]
  exact ⟨popWordState_dst _ _ _ _ _ _, popWordState_src _ _ _ _ _ _, True.intro⟩

theorem headState_frame (a : Data) (word tail address : List Bool) (i : Fin 896)
    (h838 : i ≠ 838) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (headState a word tail address).stacks i = a.stacks i := by
  simp only [headState, Function.update_of_ne h843]
  exact popWordState_outside _ _ _ _ _ _ _ h840 h838

theorem readHead_run_space (a : Data) (word tail address : List Bool)
    (hframes : a.stacks 840 = Encoding.frame word.reverse ++ tail)
    (hword : a.stacks 838 = []) (haddress : a.stacks 843 = true :: address) :
    let program := compiled readHead 840 838
    Trace program (6 * word.length + 6) (a.withPC (some program.entry))
      ((headState a word tail address).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ 6 * word.length + 6 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks + 6 * word.length + 6 := by
  refine ⟨?_, ?_⟩
  · simpa only [show 6 * word.length + 5 + 1 = 6 * word.length + 6 by omega] using
      compiled_halt_trace (readHead_eval a word tail address hframes hword haddress) 840 838
  · intro prefixSteps intermediate hp ht i
    have h := StructuredSpace.local_stack_bound (compiled readHead 840 838) le_rfl
      prefixSteps intermediate hp ht i
    simpa only [dataBits, StructuredProgram.State.withPC, Nat.add_assoc] using h

/-- The visitor copies polynomial-length retained frame/address words once.
All persistent tuple and node accumulators are included in the initial bound. -/
theorem setup_run_space (a : Data) (htmp : a.stacks 841 = []) :
    let program := compiled setup 837 840
    let steps := 7 * (a.stacks 837).length + 7 * (a.stacks 845).length + 11
    Trace program steps (a.withPC (some program.entry)) ((setupState a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks + steps := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa only [show 7 * (a.stacks 837).length + 7 * (a.stacks 845).length + 10 + 1 =
        7 * (a.stacks 837).length + 7 * (a.stacks 845).length + 11 by omega] using
      compiled_halt_trace (setup_eval a htmp) 837 840
  · intro prefixSteps intermediate hp ht
    have hb : dataBits (a.withPC (some (compiled setup 837 840).entry)) ≤ stackBits a.stacks := le_rfl
    have hh := StructuredSpace.local_stack_bound (compiled setup 837 840)
      (a := a.withPC (some (compiled setup 837 840).entry))
      (steps := 7 * (a.stacks 837).length + 7 * (a.stacks 845).length + 11) hb
      prefixSteps intermediate hp ht
    exact hh

/-- The address counts unprocessed heads above the fixed node offset. Reading
one frame decrements exactly once, even if that representative has zero bits. -/
theorem readHead_frames (a : Data) (word : List Bool) (rest : List (List Bool))
    (base : ℕ)
    (hframes : a.stacks 840 = suspendedFrames (word :: rest))
    (hword : a.stacks 838 = [])
    (haddress : a.stacks 843 = List.replicate (base + (word :: rest).length) true) :
    Eval readHead (6 * word.length + 5) a
      (headState a word (suspendedFrames rest) (List.replicate (base + rest.length) true)) := by
  apply readHead_eval
  · simpa only [suspendedFrames, List.flatMap_cons] using hframes
  · exact hword
  · simpa only [List.length_cons, Nat.add_succ, List.replicate_succ] using haddress

/-- The native frame parser restores the exact stored representative rather
than constructing a coordinate tuple from arbitrary ring values. -/
theorem readHead_frames_words (a : Data) (word : List Bool) (rest : List (List Bool))
    (base : ℕ) :
    let b := headState a word (suspendedFrames rest) (List.replicate (base + rest.length) true)
    b.stacks 838 = word ∧ b.stacks 840 = suspendedFrames rest ∧
      b.stacks 843 = List.replicate (base + rest.length) true :=
  headState_words a word (suspendedFrames rest) (List.replicate (base + rest.length) true)

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

/-- Overwriting pays for removing the old word before copying the new one.
It is used for the persistent ambient representative baseline. -/
def overwrite (src dst : Fin 896) : Code :=
  .seq (.call (StackRoutines.clearProgram dst 0 1)) (copyWord src dst 841)

noncomputable def overwriteState (src dst : Fin 896) (a : Data) : Data :=
  copyState src dst ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

/-- A peek checks whether another escaped frame exists. A zero-width head
still occupies its frame terminator and therefore enters the loop once. -/
def testFrames : Code := .base (.atom (.peek 840 0 1))

def tested (a : Data) : Data := ⟨readRegs a.regs 0 1 (a.stacks 840).head?,a.stacks⟩

theorem testFrames_eval (a : Data) : Eval testFrames 1 a (tested a) :=
  Eval.base (StructuredProgram.Eval.atom (.peek 840 0 1) a)

theorem tested_empty (a : Data) (h : a.stacks 840 = []) : (tested a).regs 1 = false := by
  simp [tested,readRegs,h]

theorem tested_cons (a : Data) (word : List Bool) (rest : List (List Bool))
    (h : a.stacks 840 = suspendedFrames (word :: rest)) : (tested a).regs 1 = true := by
  have hn : Encoding.frame word.reverse ≠ [] := by
    cases word.reverse <;> simp [Encoding.frame]
  simp [tested,readRegs,h,suspendedFrames,hn]

/-- The callback may consume or retain its parsed representative; clearing is
explicit and the next test is recomputed after its arbitrary register use. -/
def finishHead : Code := .seq (.call (StackRoutines.clearProgram 838 0 1)) testFrames

def finished (a : Data) : Data :=
  tested ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks 838 a.stacks⟩

theorem finishHead_eval (a : Data) :
    Eval finishHead (2 * (a.stacks 838).length + 4) a (finished a) := by
  have h := (clear_eval 838 a).seq (testFrames_eval _)
  simpa only [finishHead, finished, show 2 * (a.stacks 838).length + 3 + 1 =
    2 * (a.stacks 838).length + 4 by omega] using h

theorem finished_stacks (a : Data) :
    (finished a).stacks = Function.update a.stacks 838 [] := rfl

/-- The instruction table is fixed; only the retained frame stack controls
its number of head visits. The same controller is used for both passes. -/
def headBody (work : Code) : Code := .seq readHead (.seq work finishHead)
def headLoop (work : Code) : Code := .while 1 (headBody work)
def pass (work : Code) : Code := .seq setup (.seq testFrames (headLoop work))

theorem headBody_eval (work : Code) (a b : Data) (word : List Bool)
    (rest : List (List Bool)) (base steps : ℕ)
    (hframes : a.stacks 840 = suspendedFrames (word :: rest))
    (hword : a.stacks 838 = [])
    (haddress : a.stacks 843 = List.replicate (base + (word :: rest).length) true)
    (hw : Eval work steps
      (headState a word (suspendedFrames rest) (List.replicate (base + rest.length) true)) b) :
    Eval (headBody work)
      (6 * word.length + steps + 2 * (b.stacks 838).length + 9) a (finished b) := by
  have h := (readHead_frames a word rest base hframes hword haddress).seq
    (hw.seq (finishHead_eval b))
  simpa only [headBody, show 6 * word.length + 5 + (steps + (2 * (b.stacks 838).length + 4)) =
    6 * word.length + steps + 2 * (b.stacks 838).length + 9 by omega] using h

/-- The source loop records only the remaining escaped frames and one unary
address. This is a proof predicate, not an executable list of visits. -/
structure FrameCursor (base : ℕ) (words : List (List Bool)) (a : Data) : Prop where
  frames : a.stacks 840 = suspendedFrames words
  current : a.stacks 838 = []
  address : a.stacks 843 = List.replicate (base + words.length) true
  guard : a.regs 1 = !words.isEmpty

theorem finished_cursor (base : ℕ) (words : List (List Bool)) (a : Data)
    (hf : a.stacks 840 = suspendedFrames words)
    (ha : a.stacks 843 = List.replicate (base + words.length) true) :
    FrameCursor base words (finished a) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [finished_stacks,Function.update_of_ne (by decide : (840 : Fin 896) ≠ 838)] using hf
  · rw [finished_stacks,Function.update_self]
  · simpa only [finished_stacks,Function.update_of_ne (by decide : (843 : Fin 896) ≠ 838)] using ha
  · cases words with
    | nil =>
        apply tested_empty
        simpa [suspendedFrames, StackRoutines.clearStacks,
          Function.update_of_ne (by decide : (840 : Fin 896) ≠ 838)] using hf
    | cons word rest =>
        apply tested_cons _ word rest
        simpa only [StackRoutines.clearStacks,
          Function.update_of_ne (by decide : (840 : Fin 896) ≠ 838)] using hf

/-- Composition over actual callbacks. This theorem charges every frame read,
representative clear and loop test. Concrete first/second pass callbacks must
instantiate its premise; it does not assert an evaluator implementation. -/
theorem headLoop_eval (work : Code) (base C : ℕ) (I : List (List Bool) → Data → Prop)
    (step : ∀ word rest a, FrameCursor base (word :: rest) a → I (word :: rest) a →
      ∃ steps b, Eval work steps
        (headState a word (suspendedFrames rest) (List.replicate (base + rest.length) true)) b ∧
        steps ≤ C ∧ b.stacks 838 = word ∧ b.stacks 840 = suspendedFrames rest ∧
        b.stacks 843 = List.replicate (base + rest.length) true ∧ I rest (finished b))
    (words : List (List Bool)) (a : Data) (hc : FrameCursor base words a) (hi : I words a) :
    ∃ steps b, Eval (headLoop work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
      steps ≤ 8 * (words.map List.length).sum + (C + 10) * words.length + 1 := by
  induction words generalizing a with
  | nil =>
      refine ⟨1,a,Eval.while_false ?_,hc,hi,?_⟩
      · simpa using hc.guard
      · simp
  | cons word rest ih =>
      obtain ⟨nt,b,hwork,hcost,h838,h840,h843,hI⟩ := step word rest a hc hi
      have hbody := headBody_eval work a b word rest base nt hc.frames hc.current hc.address hwork
      have hnext := finished_cursor base rest b h840 h843
      obtain ⟨ns,c,hrest,hc',hi',hbound⟩ := ih (finished b) hnext hI
      refine ⟨(6 * word.length + nt + 2 * (b.stacks 838).length + 9) + ns + 1,c,
        Eval.while_true (by simpa using hc.guard) hbody hrest,hc',hi',?_⟩
      rw [h838]
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

theorem overwrite_run_space (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    let p := compiled (overwrite src dst) src dst
    ∃ steps, Trace p steps (a.withPC (some p.entry)) ((overwriteState src dst a).withPC none) ∧
      steps ≤ 9 * B + 9 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps (a.withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 905 * B + 9 := by
  dsimp only
  have hs := hb src
  have hd := hb dst
  have ht : 2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 + 1 ≤ 9 * B + 9 := by omega
  refine ⟨_,compiled_halt_trace (overwrite_eval src dst hsd hst htd a htmp) src dst,ht,?_⟩
  have hin : dataBits (a.withPC (some (compiled (overwrite src dst) src dst).entry)) ≤ 896 * B :=
    StreamResources.dataBits_le_mul _ hb
  intro prefixSteps intermediate hle htrace i
  have hx := StructuredSpace.local_stack_bound (compiled (overwrite src dst) src dst)
    (steps := 9 * B + 9) hin prefixSteps intermediate (hle.trans ht) htrace i
  omega

/-- Starting a second pass clears the previous node offset before installing
its past-the-end address. The retained representatives are copied unchanged. -/
def restart : Code := .seq (overwrite 837 840) (overwrite 845 843)

noncomputable def restartState (a : Data) : Data :=
  overwriteState 845 843 (overwriteState 837 840 a)

def restartCost (a : Data) : ℕ :=
  2 * (a.stacks 840).length + 7 * (a.stacks 837).length +
    2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 16

theorem restart_eval (a : Data) (htmp : a.stacks 841 = []) :
    Eval restart (restartCost a) a (restartState a) := by
  have h1 := overwrite_eval 837 840 (by decide) (by decide) (by decide) a htmp
  have h841 : (overwriteState 837 840 a).stacks 841 = [] :=
    (overwriteState_frame _ _ (by decide) _ _ (by decide)).trans htmp
  have h2 := overwrite_eval 845 843 (by decide) (by decide) (by decide)
    (overwriteState 837 840 a) h841
  have h843 := overwriteState_frame 837 840 (by decide) a 843 (by decide)
  have h845 := overwriteState_frame 837 840 (by decide) a 845 (by decide)
  have ht := h1.seq h2
  simpa only [restart, restartState, h843,h845,restartCost,show
    2 * (a.stacks 840).length + 7 * (a.stacks 837).length + 8 +
      (2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 8) =
    2 * (a.stacks 840).length + 7 * (a.stacks 837).length +
      2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 16 by omega] using ht

theorem restartState_words (a : Data) :
    (restartState a).stacks 840 = a.stacks 837 ∧
      (restartState a).stacks 843 = a.stacks 845 := by
  have h1 := overwriteState_stacks 837 840 (by decide) a
  have h2 := overwriteState_stacks 845 843 (by decide) (overwriteState 837 840 a)
  change (overwriteState 845 843 (overwriteState 837 840 a)).stacks 840 = a.stacks 837 ∧
    (overwriteState 845 843 (overwriteState 837 840 a)).stacks 843 = a.stacks 845
  rw [h2,h1]
  simp

theorem restartState_frame (a : Data) (i : Fin 896) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (restartState a).stacks i = a.stacks i := by
  rw [restartState,overwriteState_frame _ _ (by decide) _ _ h843,
    overwriteState_frame _ _ (by decide) _ _ h840]

theorem restartState_bound (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((restartState a).stacks i).length ≤ B :=
  overwriteState_bound 845 843 (by decide) _ B
    (overwriteState_bound 837 840 (by decide) a B hb)

theorem restartState_cursor (a : Data) (base : ℕ) (words : List (List Bool))
    (hreps : a.stacks 837 = suspendedFrames words)
    (haddr : a.stacks 845 = List.replicate (base + words.length) true)
    (hcurrent : a.stacks 838 = []) :
    FrameCursor base words (tested (restartState a)) := by
  have hf := (restartState_words a).1.trans hreps
  refine ⟨hf,?_,(restartState_words a).2.trans haddr,?_⟩
  · exact (restartState_frame a 838 (by decide) (by decide)).trans hcurrent
  · cases words with
    | nil => exact tested_empty _ hf
    | cons word rest => exact tested_cons _ word rest hf

/-- The first tuple pass installs the current representative into the full
ambient baseline. The second pass can then retain every foreign head. -/
def installRepresentative : Code :=
  .seq (overwrite 838 859)
    (.seq (.call HighQueryAdapter.NativeOverlay.prepareProgram)
      (.seq (overwrite 145 869) (.call (StackRoutines.clearProgram 859 0 1))))

noncomputable def stagedRepresentative (a : Data) : Data := overwriteState 838 859 a
noncomputable def overlaidRepresentative (a : Data) (rf : Fin 8 → Bool) : Data :=
  HighQueryAdapter.NativeOverlay.result
    (HighQueryAdapter.NativeOverlay.resetState (stagedRepresentative a)) rf
noncomputable def installedRepresentative (a : Data) (rf : Fin 8 → Bool) : Data :=
  let b := overwriteState 145 869 (overlaidRepresentative a rf)
  ⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks 859 b.stacks⟩

theorem stagedRepresentative_words (a : Data) :
    (stagedRepresentative a).stacks 859 = a.stacks 838 ∧
    (stagedRepresentative a).stacks 670 = a.stacks 670 ∧
    (stagedRepresentative a).stacks 869 = a.stacks 869 := by
  rw [stagedRepresentative,overwriteState_stacks _ _ (by decide)]
  simp

theorem installedRepresentative_baseline (a : Data) (rf : Fin 8 → Bool) :
    (installedRepresentative a rf).stacks 869 =
      SqrtLog.LeafAssignmentMergeProgram.merge
        (SqrtLog.HighIncidenceProgram.Restriction.zeroMerge (a.stacks 670) (a.stacks 838))
        (a.stacks 670) (a.stacks 869) := by
  change (StackRoutines.clearStacks 859
    (overwriteState 145 869 (overlaidRepresentative a rf)).stacks) 869 = _
  simp only [StackRoutines.clearStacks,Function.update_of_ne (by decide : (869 : Fin 896) ≠ 859),
    overwriteState_stacks 145 869 (by decide),Function.update_self]
  rw [overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_assignment]
  rw [(stagedRepresentative_words a).1,(stagedRepresentative_words a).2.1,
    (stagedRepresentative_words a).2.2]

theorem installedRepresentative_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896)
    (hi : i ∉ ([145,859,869,872,873,874,875,876,877] : List (Fin 896))) :
    (installedRepresentative a rf).stacks i = a.stacks i := by
  have h859 : i ≠ 859 := by intro h; subst i; exact hi (by simp)
  have h869 : i ≠ 869 := by intro h; subst i; exact hi (by simp)
  have hover : i ∉ HighQueryAdapter.NativeOverlay.changed := by
    intro h
    simp only [HighQueryAdapter.NativeOverlay.changed,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hi (by decide)
  simp only [installedRepresentative,StackRoutines.clearStacks,Function.update_of_ne h859]
  rw [overwriteState_frame _ _ (by decide) _ _ h869,
    overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_frame _ _ _ hover,
    stagedRepresentative,overwriteState_frame _ _ (by decide) _ _ h859]

theorem installedRepresentative_bound (a : Data) (rf : Fin 8 → Bool) (B : ℕ)
    (hh : (a.stacks 838).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((installedRepresentative a rf).stacks i).length ≤ B := by
  have hs := overwriteState_bound 838 859 (by decide) a B hb
  have hsh : ((stagedRepresentative a).stacks 859).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount ((stagedRepresentative a).stacks 670) := by
    rw [(stagedRepresentative_words a).1,(stagedRepresentative_words a).2.1]
    exact hh
  have ho := HighQueryAdapter.NativeOverlay.prepared_bound (stagedRepresentative a) rf B hsh hs
  have hc := overwriteState_bound 145 869 (by decide) (overlaidRepresentative a rf) B ho
  intro i
  change (StackRoutines.clearStacks 859
    (overwriteState 145 869 (overlaidRepresentative a rf)).stacks i).length ≤ B
  by_cases hi : i = 859
  · subst i
    simp [StackRoutines.clearStacks]
  · simpa [StackRoutines.clearStacks,hi] using hc i

theorem installRepresentative_eval (a : Data) (B : ℕ)
    (htmp : a.stacks 841 = [])
    (hh : (a.stacks 838).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps rf, Eval installRepresentative steps a (installedRepresentative a rf) ∧
      steps ≤ 90 * B + 89 := by
  have hcopy := overwrite_eval 838 859 (by decide) (by decide) (by decide) a htmp
  have hstage := stagedRepresentative_words a
  have hs := overwriteState_bound 838 859 (by decide) a B hb
  have hsh : ((stagedRepresentative a).stacks 859).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount ((stagedRepresentative a).stacks 670) := by
    rw [hstage.1,hstage.2.1]
    exact hh
  obtain ⟨nt,rf,htr,hcost,_⟩ := HighQueryAdapter.NativeOverlay.prepare_trace_space
    (stagedRepresentative a) B hsh (by simpa only [hstage.2.1,hstage.2.2] using hm) hs
  have he : Eval (.call HighQueryAdapter.NativeOverlay.prepareProgram) nt
      (stagedRepresentative a) (overlaidRepresentative a rf) := Eval.call _ htr
  have h841 : (overlaidRepresentative a rf).stacks 841 = [] := by
    rw [overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_frame _ _ _ (by decide),
      stagedRepresentative,overwriteState_frame _ _ (by decide) _ _ (by decide)]
    exact htmp
  have hsave := overwrite_eval 145 869 (by decide) (by decide) (by decide)
    (overlaidRepresentative a rf) h841
  have hclear := clear_eval 859 (overwriteState 145 869 (overlaidRepresentative a rf))
  have hout := hcopy.seq (he.seq (hsave.seq hclear))
  refine ⟨_,rf,hout,?_⟩
  have hbo := HighQueryAdapter.NativeOverlay.prepared_bound (stagedRepresentative a) rf B hsh hs
  have hbc := overwriteState_bound 145 869 (by decide) (overlaidRepresentative a rf) B hbo
  have h859 := hb 859
  have h838 := hb 838
  have h869 := hbo 869
  have h145 := hbo 145
  have hlast := hbc 859
  change ((overlaidRepresentative a rf).stacks 869).length ≤ B at h869
  change ((overlaidRepresentative a rf).stacks 145).length ≤ B at h145
  omega

/-- The concrete baseline update has a polynomial transient envelope and
returns to the same retained word bound, permitting repeated head visits. -/
theorem installRepresentative_run_space (a : Data) (B : ℕ)
    (htmp : a.stacks 841 = [])
    (hh : (a.stacks 838).length =
      SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    let p := compiled installRepresentative 838 869
    ∃ steps rf, Trace p steps (a.withPC (some p.entry))
      ((installedRepresentative a rf).withPC none) ∧ steps ≤ 90 * B + 90 ∧
      (∀ i, ((installedRepresentative a rf).stacks i).length ≤ B) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps (a.withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 986 * B + 90 := by
  dsimp only
  obtain ⟨steps,rf,he,ht⟩ := installRepresentative_eval a B htmp hh hm hb
  refine ⟨steps+1,rf,compiled_halt_trace he 838 869,by omega,
    installedRepresentative_bound a rf B hh hb,?_⟩
  have hin : dataBits (a.withPC (some (compiled installRepresentative 838 869).entry)) ≤ 896*B :=
    StreamResources.dataBits_le_mul _ hb
  intro prefixSteps intermediate hle htrace i
  have hx := StructuredSpace.local_stack_bound (compiled installRepresentative 838 869)
    (steps := 90*B+90) hin prefixSteps intermediate (by omega) htrace i
  omega

/-- The paid native update has the intended ambient-coordinate meaning;
foreign-head and fixed-high coordinates are read from the retained baseline. -/
theorem installedRepresentative_ofFn {n : ℕ} (a : Data) (rf : Fin 8 → Bool)
    (head current baseline : Fin n → Bool)
    (hmask : a.stacks 670 = List.ofFn head)
    (hrep : a.stacks 838 = SqrtLog.HighIncidenceProgram.Restriction.selected true
      (List.ofFn head) (List.ofFn current))
    (hbase : a.stacks 869 = List.ofFn baseline) :
    (installedRepresentative a rf).stacks 869 =
      List.ofFn (fun v => if head v then current v else baseline v) := by
  rw [installedRepresentative_baseline,hmask,hrep,hbase]
  exact HighQueryAdapter.Overlay.overlay_ofFn head current baseline

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
