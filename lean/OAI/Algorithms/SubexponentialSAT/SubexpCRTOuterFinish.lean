import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSetup
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSweep

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

theorem sweepStore_of_agree (f : Fin 320 → List Bool) (w : SweepWords)
    (h213 : f 213 = w.nodeCopy) (h216 : f 216 = w.indexCopy) (h225 : f 225 = w.jet)
    (h257 : f 257 = w.remaining) (h258 : f 258 = w.processed) (h259 : f 259 = w.current)
    (h260 : f 260 = w.index) (h261 : f 261 = w.accumulator) (h266 : f 266 = w.jets) :
    sweepStore f w = f := by
  funext j
  unfold sweepStore
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · subst j; exact h213.symm
  · subst j; exact h216.symm
  · subst j; exact h225.symm
  · subst j; exact h257.symm
  · subst j; exact h258.symm
  · subst j; exact h259.symm
  · subst j; exact h260.symm
  · subst j; exact h261.symm
  · subst j; exact h266.symm
  · rfl

theorem flatMap_length_of_width {I : Type*} (encode : I → List Bool) (W : ℕ)
    (hw : ∀ x, (encode x).length = W) (xs : List I) :
    (xs.flatMap encode).length = xs.length * W := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, hw, Nat.add_mul, Nat.add_comm]

def cleanupBudget (W J Q D : ℕ) : ℕ :=
  2 * W + 4 * Q * W + 2 * Q + 2 * D + 2 * J + 24

theorem cleanup_ready_cost {I A : Type*}
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (W J D : ℕ) (full : List I) (a : A) (regs : Fin 16 → Bool)
    (frame : Fin 320 → List Bool) (hw : ∀ x, (encode x).length = W)
    (h104 : (frame 104).length = W)
    (h214 : (frame 214).length = full.length * W)
    (h268 : (frame 268).length ≤ D) (h277 : (frame 277).length = J) :
    SubexpSetupStorage.clearManyCost [104,214,257,258,260,266,268,277]
      (sweepState regs frame (readyWords encode jet encodeAcc full.reverse [] a)) ≤
      cleanupBudget W J full.length D := by
  have hlen := flatMap_length_of_width encode W hw full.reverse
  simp only [List.length_reverse] at hlen
  have hsum := flatMap_length_of_width encode W hw full
  simp only [List.length_flatMap] at hsum
  simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, sweepState,
    sweepStore, readyWords, h104, h214, h277, cleanupBudget]
  nlinarith [hsum]

def loopAndCleanup (middle : Code) : Code :=
  .seq testNodes (.seq (sweepLoop middle) cleanup)

/-- Complete actual traversal and cleanup, with the physical output stack
identified. Cleanup includes the copied full node list and generated widths. -/
theorem loopAndCleanup_run {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (frame : Fin 320 → List Bool)
    (middle : Code) (W J D K : ℕ) (full : List I)
    (hw : ∀ i, (encode i).length = W) (hj : ∀ i, (jet i).length = J) (hpos : 0 < W)
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (h104 : (frame 104).length = W) (h277 : (frame 277).length = J)
    (h214 : (frame 214).length = full.length * W) (h268 : (frame 268).length ≤ D)
    (hmid : ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
      ∀ rr, ∃ n ≤ K, ∃ rf b,
        Eval middle n
          (sweepState rr frame (loadedReady encode jet encodeAcc processed remaining item acc))
          (sweepState rf frame (loadedReady encode jet encodeAcc processed remaining item b)) ∧
        value b = value acc + term item)
    (a : A) (regs : Fin 16 → Bool) :
    ∃ n ≤ full.length * (K + transportCost W J full.length + 2) +
        cleanupBudget W J full.length D + 2,
      ∃ (out : Data) (b : A),
        Eval (loopAndCleanup middle) n
          (sweepState regs frame (readyWords encode jet encodeAcc [] full a)) out ∧
        out.stacks 261 = encodeAcc b ∧ value b = value a + (full.map term).sum ∧
        (∀ j ∈ ([104,214,257,258,260,266,268,277] : List (Fin 320)), out.stacks j = []) := by
  have htest := testNodes_run regs frame (readyWords encode jet encodeAcc [] full a)
  obtain ⟨n, hn, rf, b, hloop, hb⟩ := sweepLoop_run encode jet encodeAcc value term frame
    middle W J K full hw hj hpos ht hu hv h104 h277 hmid [] full a regs (by simp)
  simp only [List.append_nil] at hloop
  let last := sweepState rf frame (readyWords encode jet encodeAcc full.reverse [] b)
  have hclear := clearMany_run last [104,214,257,258,260,266,268,277]
  have hcost := cleanup_ready_cost encode jet encodeAcc W J D full b rf frame hw
    h104 h214 h268 h277
  change SubexpSetupStorage.clearManyCost [104,214,257,258,260,266,268,277] last ≤
    cleanupBudget W J full.length D at hcost
  have hrun := htest.seq (hloop.seq hclear)
  refine ⟨_, ?_, _, b, hrun, ?_, hb, ?_⟩
  · omega
  · rw [SubexpSetupStorage.clearMany_stacks]
    simp [last, sweepState, readyWords]
  · intro j hj
    rw [SubexpSetupStorage.clearMany_stacks, ite_eq_left hj]

def initialCleanPorts : List (Fin 320) :=
  [104,261,268,277,278,279,316,317,318,214,257,266] ++ [213,216,225,258,259,260]

def controller (middle : Code) : Code := .seq initializeOuter (loopAndCleanup middle)

def controllerBudget (B D Q K : ℕ) : ℕ :=
  initializationBudget B D (Q * (4 * B)) (Q * (D * (4 * B))) +
    Q * (K + transportCost (4 * B) (D * (4 * B)) Q + 2) +
    cleanupBudget (4 * B) (D * (4 * B)) Q D + 2

/-- Join physical initialization, ordered traversal and final cleanup. The
sole remaining service premise is the arithmetic middle's actual execution
on each exact loaded state, for the binary exponent produced by initialization. -/
theorem controller_run {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (middle : Code)
    (d : Data) (D K : ℕ) (full : List I) (zero : A)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ initialCleanPorts, d.stacks j = [])
    (hwidth : ∀ i, (encode i).length = 4 * (d.stacks 202).length)
    (hjet : ∀ i, (jet i).length = D * (4 * (d.stacks 202).length))
    (hpos : 0 < (d.stacks 202).length)
    (hnodes : d.stacks 256 = full.flatMap encode)
    (hjets : d.stacks 265 = full.flatMap jet)
    (hz : encodeAcc zero = List.replicate (4 * (d.stacks 202).length) false)
    (hvz : value zero = 0)
    (hmid : ∀ exponent, BinaryArithmetic.toNat exponent = D → exponent.length ≤ D →
      ∀ processed remaining item acc, full = processed.reverse ++ item :: remaining →
      ∀ rr, ∃ n ≤ K, ∃ rf b,
        Eval middle n
          (sweepState rr (initializedStacks d D exponent)
            (loadedReady encode jet encodeAcc processed remaining item acc))
          (sweepState rf (initializedStacks d D exponent)
            (loadedReady encode jet encodeAcc processed remaining item b)) ∧
        value b = value acc + term item) :
    ∃ n ≤ controllerBudget (d.stacks 202).length D full.length K,
      ∃ (out : Data) (b : A), Eval (controller middle) n d out ∧
        out.stacks 261 = encodeAcc b ∧ value b = (full.map term).sum := by
  have hc (j : Fin 320) (hj : j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] :
      List (Fin 320))) : d.stacks j = [] :=
    hclean j (List.mem_append_left _ hj)
  obtain ⟨ni, hni, ri, exponent, hi, he, hl⟩ := initializeOuter_run d D hd hc
  let f := initializedStacks d D exponent
  have hready : (⟨ri, f⟩ : Data) =
      sweepState ri f (readyWords encode jet encodeAcc [] full zero) := by
    refine SubexpScanPrimitives.state_ext rfl ?_
    refine (sweepStore_of_agree f _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
    all_goals simp [f, initializedStacks, readyWords, hnodes, hjets, hz,
      hclean 213 (by decide), hclean 216 (by decide), hclean 225 (by decide),
      hclean 258 (by decide), hclean 259 (by decide), hclean 260 (by decide)]
  have hw : (f 104).length = 4 * (d.stacks 202).length := by simp [f, initializedStacks]
  have hjw : (f 277).length = D * (4 * (d.stacks 202).length) := by
    simp [f, initializedStacks]
  have hnw : (f 214).length = full.length * (4 * (d.stacks 202).length) := by
    simpa [f, initializedStacks, hnodes] using flatMap_length_of_width encode _ hwidth full
  obtain ⟨nl, hnl, out, b, hrun, hout, hvalue, hcleared⟩ :=
    loopAndCleanup_run encode jet encodeAcc value term f middle
      (4 * (d.stacks 202).length) (D * (4 * (d.stacks 202).length)) D K full
      hwidth hjet (by omega)
      (by simpa [f, initializedStacks] using hc 278 (by simp))
      (by simpa [f, initializedStacks] using hc 279 (by simp))
      (by simpa [f, initializedStacks] using hc 318 (by simp))
      hw hjw hnw (by simpa [f, initializedStacks] using hl)
      (hmid exponent he hl) zero ri
  rw [← hready] at hrun
  have hnlen := flatMap_length_of_width encode _ hwidth full
  have hjlen := flatMap_length_of_width jet _ hjet full
  rw [hnodes, hjets, hnlen, hjlen] at hni
  refine ⟨ni + nl, ?_, out, b, hi.seq hrun, hout, ?_⟩
  · unfold controllerBudget
    omega
  · simpa only [hvz, zero_add] using hvalue

/-- With the fixed input order, the physically counted index is the current
node's original index, even though processed nodes are stored in reverse. -/
theorem traversal_index {Q : ℕ} (processed remaining : List (Fin Q)) (current : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ current :: remaining) :
    processed.length = current.val := by
  have hn := List.nodup_finRange Q
  rw [hfull] at hn
  have hm := List.nodup_cons.mp (List.nodup_middle.mp hn)
  have hnot : current ∉ processed.reverse := by
    intro h
    exact hm.1 (List.mem_append_left _ h)
  have hi := congrArg (List.idxOf current) hfull
  rw [List.idxOf_finRange, List.idxOf_append_of_notMem hnot,
    List.idxOf_cons_self, List.length_reverse, Nat.add_zero] at hi
  exact hi.symm

/-- The actual remaining ++ processed cofactor stream contains each other
node exactly once. No cancellation and no nonzero-node assumption is used. -/
theorem cofactor_stream_product {Q : ℕ} {R : Type*} [CommMonoid R]
    (processed remaining : List (Fin Q)) (current : Fin Q) (f : Fin Q → R)
    (hfull : List.finRange Q = processed.reverse ++ current :: remaining) :
    ((remaining ++ processed).map f).prod = ∏ i ∈ Finset.univ.erase current, f i := by
  have hn := List.nodup_finRange Q
  rw [hfull] at hn
  have hm := List.nodup_cons.mp (List.nodup_middle.mp hn)
  have hset : (processed.reverse ++ remaining).toFinset = Finset.univ.erase current := by
    ext j
    simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hj he
      subst j
      exact hm.1 hj
    · intro hne
      have hj : j ∈ processed.reverse ++ current :: remaining := by
        rw [← hfull]
        exact List.mem_finRange j
      rcases List.mem_append.mp hj with hp | hr
      · exact List.mem_append_left _ hp
      · rcases List.mem_cons.mp hr with he | hr
        · exact False.elim (hne he)
        · exact List.mem_append_right _ hr
  calc
    ((remaining ++ processed).map f).prod = ((processed.reverse ++ remaining).map f).prod := by
      simp [List.map_append, List.prod_append, List.map_reverse, List.prod_reverse, mul_comm]
    _ = (processed.reverse ++ remaining).toFinset.prod f := (List.prod_toFinset f hm.2).symm
    _ = ∏ i ∈ Finset.univ.erase current, f i := by rw [hset]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
