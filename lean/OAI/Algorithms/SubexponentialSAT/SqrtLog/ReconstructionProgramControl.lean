import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramSetup

namespace OAI.Algorithms

/-! Fixed-table outer Hermite traversal for arbitrary coefficient width.
Only the arithmetic middle is parameterized; this module charges all input
copying, node/jet transport, indexing, iteration and final cleanup. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

def controller (middle : Code) : Code := .seq initializeCode (loopAndCleanup middle)

def controllerBudget (W D Q K : ℕ) : ℕ :=
  initializationBudget W D (Q * W) (Q * (D * W)) +
    Q * (K + transportCost W (D * W) Q + 2) +
    cleanupBudget W (D * W) Q D + 2

/-- Join physical initialization, ordered traversal and final cleanup. The
sole remaining service premise is the arithmetic middle's actual execution
on each exact loaded state, for the binary exponent produced by initialization. -/
theorem controller_run {I A R : Type*} [AddMonoid R]
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
        out.stacks 261 = encodeAcc b ∧ value b = (full.map term).sum := by
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
  obtain ⟨nl, hnl, out, b, hrun, hout, hvalue, hcleared⟩ :=
    loopAndCleanup_run encode jet encodeAcc value term f middle
      ((d.stacks 280).length) (D * ((d.stacks 280).length)) D K full
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


end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
