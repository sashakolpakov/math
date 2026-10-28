import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterControl

namespace OAI.Algorithms

/-! Ordered execution of the concrete outer CRT tape loop. The only remaining
premise is an actual execution of its arithmetic middle command on the exact
loaded state; all loading, index updates, traversal guards, and transport costs
are discharged here. This premise is instantiated by the concrete CRT services.
-/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def sweepIteration (middle : Code) : Code :=
  .seq loadCurrent (.seq middle advance)

def sweepLoop (middle : Code) : Code :=
  .while 15 (.seq (sweepIteration middle) testNodes)

def readyWords {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (acc : A) : SweepWords :=
  { remaining := remaining.flatMap encode
    processed := processed.flatMap encode
    index := List.replicate processed.length false
    accumulator := encodeAcc acc
    jets := remaining.flatMap jet }

def loadedReady {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (item : I) (acc : A) :
    SweepWords :=
  loadedWords (readyWords encode jet encodeAcc processed (item :: remaining) acc)
    (encode item) (remaining.flatMap encode) (jet item) (remaining.flatMap jet)

theorem advanced_loadedReady {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (item : I) (acc : A) :
    advancedWords (loadedReady encode jet encodeAcc processed remaining item acc) =
      readyWords encode jet encodeAcc (item :: processed) remaining acc := by
  simp [advancedWords, cleanedWords, loadedReady, loadedWords, readyWords,
    List.replicate_succ]

theorem loadedReady_change_acc {I A : Type*} (encode : I → List Bool) (jet : I → List Bool)
    (encodeAcc : A → List Bool) (processed remaining : List I) (item : I) (a b : A) :
    {loadedReady encode jet encodeAcc processed remaining item a with
      accumulator := encodeAcc b} =
      loadedReady encode jet encodeAcc processed remaining item b := rfl

theorem testNodes_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) :
    Eval testNodes 1 (sweepState regs frame w)
      (sweepState (readRegs regs 0 15 w.remaining.head?) frame w) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.peek 257 0 15)
    (sweepState regs frame w))
  simpa only [testNodes, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    sweepState, sweepStore_remaining] using h

/-- Physical per-node cost, excluding the arithmetic middle command. The
index copy contributes nine steps per already processed node. -/
def transportCost (nodeWidth jetWidth index : ℕ) : ℕ :=
  32 * nodeWidth + 9 * index + 16 * jetWidth + 51

theorem sweepIteration_run {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (frame : Fin 320 → List Bool)
    (middle : Code) (nodeWidth jetWidth K : ℕ)
    (hwidth : ∀ i, (encode i).length = nodeWidth)
    (hjetWidth : ∀ i, (jet i).length = jetWidth)
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (hw : (frame 104).length = nodeWidth) (hjw : (frame 277).length = jetWidth)
    (processed remaining : List I) (item : I) (acc : A) (regs : Fin 16 → Bool)
    (hmid : ∀ rr, ∃ n ≤ K, ∃ rf b,
      Eval middle n
        (sweepState rr frame (loadedReady encode jet encodeAcc processed remaining item acc))
        (sweepState rf frame (loadedReady encode jet encodeAcc processed remaining item b)) ∧
      value b = value acc + term item) :
    ∃ n ≤ K + transportCost nodeWidth jetWidth processed.length, ∃ rf b,
      Eval (sweepIteration middle) n
        (sweepState regs frame (readyWords encode jet encodeAcc processed (item :: remaining) acc))
        (sweepState rf frame (readyWords encode jet encodeAcc (item :: processed) remaining b)) ∧
      value b = value acc + term item := by
  have hload := loadCurrent_run regs frame
    (readyWords encode jet encodeAcc processed (item :: remaining) acc)
    (encode item) (remaining.flatMap encode) (jet item) (remaining.flatMap jet)
    (by simp [readyWords]) (by simp [readyWords]) rfl rfl rfl rfl ht hu hv
    (hw.trans (hwidth item).symm) (hjw.trans (hjetWidth item).symm)
  obtain ⟨n, hn, rf, b, hmiddle, hvalue⟩ := hmid (readRegs regs 0 1 none)
  have hadvance := advance_run rf frame
    (loadedReady encode jet encodeAcc processed remaining item b) hv
  rw [advanced_loadedReady] at hadvance
  have h := hload.seq (hmiddle.seq hadvance)
  refine ⟨_, ?_, _, b, h, hvalue⟩
  simp only [readyWords, loadedReady, loadedWords, List.length_replicate,
    hwidth, hjetWidth, transportCost] at *
  omega

/-- The loop invariant records physical processed order, remaining order,
matching jet order, and the unary index. The arithmetic premise is an actual
finite-program trace, not a supplied answer or cost annotation. -/
theorem sweepLoop_run {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (frame : Fin 320 → List Bool)
    (middle : Code) (nodeWidth jetWidth K : ℕ) (full : List I)
    (hwidth : ∀ i, (encode i).length = nodeWidth)
    (hjetWidth : ∀ i, (jet i).length = jetWidth) (hpos : 0 < nodeWidth)
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (hw : (frame 104).length = nodeWidth) (hjw : (frame 277).length = jetWidth)
    (hmid : ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
      ∀ rr, ∃ n ≤ K, ∃ rf b,
        Eval middle n
          (sweepState rr frame (loadedReady encode jet encodeAcc processed remaining item acc))
          (sweepState rf frame (loadedReady encode jet encodeAcc processed remaining item b)) ∧
        value b = value acc + term item)
    (processed remaining : List I) (acc : A) (regs : Fin 16 → Bool)
    (hfull : full = processed.reverse ++ remaining) :
    ∃ n ≤ remaining.length * (K + transportCost nodeWidth jetWidth full.length + 2) + 1,
      ∃ rf b,
        Eval (sweepLoop middle) n
          (sweepState (readRegs regs 0 15 (remaining.flatMap encode).head?) frame
            (readyWords encode jet encodeAcc processed remaining acc))
          (sweepState rf frame
            (readyWords encode jet encodeAcc (remaining.reverse ++ processed) [] b)) ∧
        value b = value acc + (remaining.map term).sum := by
  induction remaining generalizing processed acc regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 15 none, acc, ?_, by simp⟩
      exact Eval.while_false (by simp [sweepState, readRegs])
  | cons item rest ih =>
      let r0 := readRegs regs 0 15 ((item :: rest).flatMap encode).head?
      obtain ⟨n, hn, r1, a1, hstep, hvalue⟩ :=
        sweepIteration_run encode jet encodeAcc value term frame middle nodeWidth jetWidth K
          hwidth hjetWidth ht hu hv hw hjw processed rest item acc r0
          (hmid processed rest item acc hfull)
      have hp := testNodes_run r1 frame
        (readyWords encode jet encodeAcc (item :: processed) rest a1)
      have hfull' : full = (item :: processed).reverse ++ rest := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hfull
      obtain ⟨m, hm, rf, b, hrest, hvrest⟩ := ih (item :: processed) a1 r1 hfull'
      have hg : (sweepState r0 frame
          (readyWords encode jet encodeAcc processed (item :: rest) acc)).regs 15 = true := by
        have hne : encode item ≠ [] := by
          intro hz
          have := hwidth item
          simp only [hz, List.length_nil] at this
          omega
        cases he : encode item with
        | nil => exact False.elim (hne he)
        | cons bit bits => simp [r0, sweepState, readRegs, he]
      have hrun := Eval.while_true hg (hstep.seq hp) hrest
      have hlen : processed.length ≤ full.length := by
        have h := congrArg List.length hfull
        simp only [List.length_append, List.length_reverse, List.length_cons] at h
        omega
      have hcost : transportCost nodeWidth jetWidth processed.length ≤
          transportCost nodeWidth jetWidth full.length := by
        unfold transportCost
        omega
      refine ⟨n + 1 + m + 1, ?_, rf, b, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [sweepLoop, readyWords, List.reverse_cons, List.append_assoc,
          List.singleton_append] using hrun
      · rw [hvrest, hvalue]
        simp only [List.map_cons, List.sum_cons, add_assoc]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
