import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramControl

namespace OAI.Algorithms

/-! Fixed-table outer Hermite traversal for arbitrary coefficient width.
Only the arithmetic middle is parameterized; this module charges all input
copying, node/jet transport, indexing, iteration and final cleanup. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

/-- Join physical initialization, ordered traversal and final cleanup. The
sole remaining service premise is the arithmetic middle's actual execution
on each exact loaded state, for the binary exponent produced by initialization. -/
theorem controller_run_framed {I A R : Type*} [AddMonoid R]
    (encode : I → List Bool) (jet : I → List Bool) (encodeAcc : A → List Bool)
    (value : A → R) (term : I → R) (middle : Code)
    (d : Data) (D K : ℕ) (full : List I) (zero : A)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ initialCleanPorts, d.stacks j = [])
    (hwidth : ∀ i, (encode i).length = (d.stacks 280).length)
    (hjet : ∀ i, (jet i).length = D * ((d.stacks 280).length))
    (hpos : 0 < (d.stacks 280).length)
    (hnodes : d.stacks 256 = full.flatMap encode)
    (hjets : d.stacks 265 = full.flatMap jet)
    (hz : encodeAcc zero = d.stacks 280)
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
    ∃ n ≤ controllerBudget (d.stacks 280).length D full.length K,
      ∃ (out : Data) (b : A), Eval (controller middle) n d out ∧
        out.stacks = Function.update d.stacks 261 (encodeAcc b) ∧ value b = (full.map term).sum := by
  have hc (j : Fin 320) (hj : j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] :
      List (Fin 320))) : d.stacks j = [] :=
    hclean j (List.mem_append_left _ hj)
  obtain ⟨ni, hni, ri, exponent, hi, he, hl⟩ := initialize_run d D hd hc
  let f := initializedStacks d D exponent
  have hready : (⟨ri, f⟩ : Data) =
      sweepState ri f (readyWords encode jet encodeAcc [] full zero) := by
    refine SubexpScanPrimitives.state_ext rfl ?_
    refine (sweepStore_of_agree f _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).symm
    all_goals simp [f, initializedStacks, readyWords, hnodes, hjets, hz,
      hclean 213 (by decide), hclean 216 (by decide), hclean 225 (by decide),
      hclean 258 (by decide), hclean 259 (by decide), hclean 260 (by decide)]
  have hw : (f 104).length = (d.stacks 280).length := by simp [f, initializedStacks]
  have hjw : (f 277).length = D * ((d.stacks 280).length) := by
    simp [f, initializedStacks]
  have hnw : (f 214).length = full.length * ((d.stacks 280).length) := by
    simpa [f, initializedStacks, hnodes] using flatMap_length_of_width encode _ hwidth full
  have htest := testNodes_run ri f (readyWords encode jet encodeAcc [] full zero)
  obtain ⟨nl, hnl, rf, b, hloop, hvalue⟩ := sweepLoop_run encode jet encodeAcc value term f
    middle (d.stacks 280).length (D * (d.stacks 280).length) K full hwidth hjet hpos
    (by simpa [f, initializedStacks] using hc 278 (by simp))
    (by simpa [f, initializedStacks] using hc 279 (by simp))
    (by simpa [f, initializedStacks] using hc 318 (by simp))
    hw hjw (hmid exponent he hl) [] full zero ri (by simp)
  simp only [List.append_nil] at hloop
  let last := sweepState rf f (readyWords encode jet encodeAcc full.reverse [] b)
  let out := SubexpSetupStorage.clearManyState [104,214,257,258,260,266,268,277] last
  have hclear := clearMany_run last [104,214,257,258,260,266,268,277]
  have hcost := cleanup_ready_cost encode jet encodeAcc (d.stacks 280).length
    (D * (d.stacks 280).length) D full b rf f hwidth hw hnw
    (by simpa [f, initializedStacks] using hl) hjw
  change SubexpSetupStorage.clearManyCost [104,214,257,258,260,266,268,277] last ≤
    cleanupBudget (d.stacks 280).length (D * (d.stacks 280).length) full.length D at hcost
  have hrun := htest.seq (hloop.seq hclear)
  rw [← hready] at hrun
  have hnlen := flatMap_length_of_width encode _ hwidth full
  have hjlen := flatMap_length_of_width jet _ hjet full
  rw [hnodes, hjets, hnlen, hjlen] at hni
  refine ⟨_, ?_, out, b, hi.seq hrun, ?_, ?_⟩
  · unfold controllerBudget
    omega
  · funext j
    simp only [out, SubexpSetupStorage.clearMany_stacks]
    by_cases hj : j ∈ ([104,214,257,258,260,266,268,277] : List (Fin 320))
    · rw [ite_eq_left hj]
      have hj261 : j ≠ (261 : Fin 320) := by
        intro he; subst j; simp at hj
      rw [Function.update_of_ne hj261]
      exact (hclean j (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide)).symm
    · rw [ite_eq_right hj]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      have hj104 := hj.1
      have hj214 := hj.2.1
      have hj257 := hj.2.2.1
      have hj258 := hj.2.2.2.1
      have hj260 := hj.2.2.2.2.1
      have hj266 := hj.2.2.2.2.2.1
      have hj268 := hj.2.2.2.2.2.2.1
      have hj277 := hj.2.2.2.2.2.2.2
      by_cases h213 : j = 213 <;> by_cases h216 : j = 216 <;>
        by_cases h225 : j = 225 <;> by_cases h259 : j = 259 <;> by_cases h261 : j = 261 <;>
        simp [last, sweepState, sweepStore, readyWords, f, initializedStacks, hj104, hj214, hj257, hj258, hj260, hj266, hj268, hj277,
          h213, h216, h225, h259, h261, hclean 213 (by decide), hclean 216 (by decide),
          hclean 225 (by decide), hclean 259 (by decide)]
  · simpa only [hvz, zero_add] using hvalue


end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
