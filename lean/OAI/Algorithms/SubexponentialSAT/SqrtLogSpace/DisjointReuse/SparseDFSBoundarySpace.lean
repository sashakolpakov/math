import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseAccumulatorProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

/-! Physical storage at the depth-first controller boundary.

Only framed formula bodies occur on the pending stack. The mathematical depth
is a proof index and is not serialized. Both children, the current formula,
the declared-variable word, and the two count words are charged simultaneously.
These bounds apply to the actual fixed frontier and accumulator routines after
injective port relocation. The final DFS must still establish its boundary
invariant and bounds for the concrete selector, splitter, and leaf commands.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

open BitProgram StructuredCalls

private theorem stackBits_single_le {S : ℕ} (words : Fin S → List Bool) (i : Fin S) :
    (words i).length ≤ stackBits words :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((words j).length)) (Finset.mem_univ i)

/-- Actual cleanup never increases any stack, at any prefix. No bound on
elapsed time is needed: its finite table contains only pop, branch and halt. -/
theorem clearProgram_stack_length_le {r s steps : ℕ}
    (src : Fin s) (value present : Fin r) {a b : Cfg r s 3}
    (htrace : Trace (StackRoutines.clearProgram src value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
  have hstep {a b : Cfg r s 3}
      (hs : step (StackRoutines.clearProgram src value present) a = some b) :
      ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some label =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        intro i
        fin_cases label
        · by_cases hi : i = src
          · subst i
            simp [execInstr]
          · simp [execInstr, hi]
        · simp [execInstr]
        · simp [execInstr]
  induction htrace with
  | refl => exact fun _ => le_rfl
  | cons hs ht ih => exact fun i => (ih i).trans (hstep hs i)

def frontierBound (bodyBound depth : ℕ) : ℕ :=
  1 + (2 * bodyBound + 2) * (depth + 2)

def storageBound (bodyBound depth thresholdBound n : ℕ) : ℕ :=
  frontierBound bodyBound depth + thresholdBound + 100 * (bodyBound + n + 1)

/-- The delimiter and every escaped body bit are included. -/
theorem frontier_length_le (bodies : List (List Bool)) (bodyBound depth : ℕ)
    (hdepth : bodies.length ≤ depth + 2)
    (hbodies : ∀ body ∈ bodies, body.length ≤ bodyBound) :
    (Encoding.encodeList id bodies).length ≤ frontierBound bodyBound depth := by
  exact (Encoding.length_encodeList_upper id bodies bodyBound hbodies).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hdepth) _)

/-- The finite DFS port view. Scratch and all other selector ports are empty
at this boundary; `rootEmbedding` puts persistent words above the leaf bank. -/
def boundaryStacks (current threshold pending saved left right total leaf : List Bool) :
    Fin 31 → List Bool :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], current, [], [], [], [], [],
    threshold, [], [], [], [], pending, saved, left, right, total, leaf, []]

theorem boundary_stackBits (current threshold pending saved left right total leaf : List Bool) :
    stackBits (boundaryStacks current threshold pending saved left right total leaf) =
      current.length + threshold.length + pending.length + saved.length +
        left.length + right.length + total.length + leaf.length := by
  simp [stackBits, boundaryStacks, Fin.sum_univ_succ, Nat.add_assoc]

/-- Count words are canonical, so cancellation or redundant zero padding
cannot invalidate this actual byte-length bound. The two framed children may
coexist with the original formula and the complete pending frontier. -/
theorem boundary_space (current threshold left right : List Bool)
    (bodies : List (List Bool)) (a b n bodyBound depth thresholdBound : ℕ)
    (hcurrent : current.length ≤ bodyBound)
    (hthreshold : threshold.length ≤ thresholdBound)
    (hleft : left.length ≤ 2 * bodyBound + 2)
    (hright : right.length ≤ 2 * bodyBound + 2)
    (hdepth : bodies.length ≤ depth + 2)
    (hbodies : ∀ body ∈ bodies, body.length ≤ bodyBound)
    (hcount : a + b ≤ 2 ^ n) :
    stackBits (boundaryStacks current threshold (Encoding.encodeList id bodies)
      (Encoding.encodeNat n) left right (binaryNat a) (binaryNat b)) ≤
      storageBound bodyBound depth thresholdBound n := by
  have hpending := frontier_length_le bodies bodyBound depth hdepth hbodies
  have ha := binaryNat_length_le ((Nat.le_add_right a b).trans hcount)
  have hb := binaryNat_length_le ((Nat.le_add_left b a).trans hcount)
  rw [boundary_stackBits, Encoding.length_encodeNat]
  unfold storageBound
  omega

/-- Local current, saved-n, pending and scratch ports. -/
def popStack : Fin 4 ↪ Fin 31 where
  toFun := ![13, 25, 24, 23]
  inj' := by decide

/-- Local pending, saved-n, framed children and scratch ports. -/
def pairStack : Fin 5 ↪ Fin 31 where
  toFun := ![24, 25, 26, 27, 0]
  inj' := by decide

/-- Local running total, current leaf count and scratch ports. -/
def countStack : Fin 3 ↪ Fin 31 where
  toFun := ![28, 29, 30]
  inj' := by decide

/-- DFS bookkeeping retains its original ports inside the frozen 1220-stack ABI.
Current formula, threshold, frontier, header and counts lie above its low scratch bank.
View port zero remains scratch, while view port thirteen is the formula. -/
def rootEmbedding : Fin 31 ↪ Fin 1220 where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 265, 14, 15, 16, 17, 18,
    259, 20, 21, 22, 23, 257, 258, 261, 262, 260, 263, 30]
  inj' := by decide

private theorem rootEmbedding_avoids (i : Fin 31) :
    rootEmbedding i ≠ 256 ∧ rootEmbedding i ≠ 264 ∧ rootEmbedding i ≠ 266 := by
  exact (by decide : ∀ j : Fin 31,
    rootEmbedding j ≠ 256 ∧ rootEmbedding j ≠ 264 ∧ rootEmbedding j ≠ 266) i

/-- Full root boundary stacks, including retained raw input and the two
binary setup parameters. Every unassigned stack is empty. -/
noncomputable def rootStacks (raw current threshold pending saved left right total leaf
    d sparseParameter : List Bool) : Fin 1220 → List Bool :=
  Function.update (Function.update (Function.update
    (Function.extend rootEmbedding
      (boundaryStacks current threshold pending saved left right total leaf) (fun _ => []))
    256 raw) 264 d) 266 sparseParameter

theorem rootStacks_view (raw current threshold pending saved left right total leaf
    d sparseParameter : List Bool) (i : Fin 31) :
    rootStacks raw current threshold pending saved left right total leaf d sparseParameter
      (rootEmbedding i) =
      boundaryStacks current threshold pending saved left right total leaf i := by
  obtain ⟨hraw, hd, hs⟩ := rootEmbedding_avoids i
  simp only [rootStacks, Function.update_of_ne hs, Function.update_of_ne hd,
    Function.update_of_ne hraw, rootEmbedding.injective.extend_apply]

theorem rootStacks_reserved (raw current threshold pending saved left right total leaf
    d sparseParameter : List Bool) (i : Fin 1220) (hi : 267 ≤ i.val) :
    rootStacks raw current threshold pending saved left right total leaf d sparseParameter i = [] := by
  have hraw : i ≠ 256 := by intro h; subst i; exact (by omega)
  have hd : i ≠ 264 := by intro h; subst i; exact (by omega)
  have hs : i ≠ 266 := by intro h; subst i; exact (by omega)
  have hview : ¬ ∃ j, rootEmbedding j = i := by
    rintro ⟨j, rfl⟩
    have hj := (by decide : ∀ q : Fin 31, (rootEmbedding q).val < 267) j
    omega
  simp only [rootStacks, Function.update_of_ne hs, Function.update_of_ne hd,
    Function.update_of_ne hraw, Function.extend_apply' _ _ _ hview]

/-- All 1220 stacks are bounded, including raw input and setup data outside
the finite DFS view. The reserved high bank is empty in this exact state. -/
theorem root_boundary_space (raw current threshold left right d sparseParameter : List Bool)
    (bodies : List (List Bool)) (a b n bodyBound depth thresholdBound : ℕ)
    (hcurrent : current.length ≤ bodyBound)
    (hthreshold : threshold.length ≤ thresholdBound)
    (hleft : left.length ≤ 2 * bodyBound + 2)
    (hright : right.length ≤ 2 * bodyBound + 2)
    (hdepth : bodies.length ≤ depth + 2)
    (hbodies : ∀ body ∈ bodies, body.length ≤ bodyBound)
    (hcount : a + b ≤ 2 ^ n) :
    ∀ i, (rootStacks raw current threshold (Encoding.encodeList id bodies)
      (Encoding.encodeNat n) left right (binaryNat a) (binaryNat b) d sparseParameter i).length ≤
      storageBound bodyBound depth
        (thresholdBound + raw.length + d.length + sparseParameter.length) n := by
  have hbits := boundary_space current threshold left right bodies a b n bodyBound depth
    thresholdBound hcurrent hthreshold hleft hright hdepth hbodies hcount
  intro i
  by_cases hraw : i = 256
  · subst i
    simp only [rootStacks, Function.update_of_ne (by decide : (256 : Fin 1220) ≠ 266),
      Function.update_of_ne (by decide : (256 : Fin 1220) ≠ 264), Function.update_self]
    unfold storageBound
    omega
  by_cases hd : i = 264
  · subst i
    simp only [rootStacks, Function.update_of_ne (by decide : (264 : Fin 1220) ≠ 266),
      Function.update_self]
    unfold storageBound
    omega
  by_cases hs : i = 266
  · subst i
    simp only [rootStacks, Function.update_self]
    unfold storageBound
    omega
  by_cases hi : ∃ j, rootEmbedding j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [rootStacks_view]
    have hj : (boundaryStacks current threshold (Encoding.encodeList id bodies)
        (Encoding.encodeNat n) left right (binaryNat a) (binaryNat b) j).length ≤
        stackBits (boundaryStacks current threshold (Encoding.encodeList id bodies)
          (Encoding.encodeNat n) left right (binaryNat a) (binaryNat b)) :=
      stackBits_single_le _ j
    unfold storageBound at *
    omega
  · simp only [rootStacks, Function.update_of_ne hs, Function.update_of_ne hd,
      Function.update_of_ne hraw, Function.extend_apply' _ _ _ hi, List.length_nil,
      Nat.zero_le]

/-- The pop's actual transient scratch is bounded independently of how many
earlier DFS iterations have run. Unmapped caller stacks retain their bound. -/
theorem pop_lifted_space {R S : ℕ} (register : Fin 3 ↪ Fin R)
    (ambient : Fin 31 ↪ Fin S)
    (frame : Cfg R S (size SparseFrontierProgram.popIfPresent + 1))
    (body saved pending : List Bool) (v p flag : Bool)
    (bodyBound depth thresholdBound n : ℕ)
    (hbody : body.length ≤ bodyBound) (hsaved : saved.length ≤ n + 1)
    (hpending : pending.length ≤ frontierBound bodyBound depth)
    (hframe : ∀ i, (frame.stacks i).length ≤
      storageBound bodyBound depth thresholdBound n) :
    ∀ prefixSteps c, prefixSteps ≤ 9 * body.length + 11 →
      Trace (ProgramLinking.liftProgram SparseFrontierProgram.popIfPresentProgram
        register (ambient ∘ popStack)) prefixSteps
        (ProgramLinking.embedCfg register (ambient ∘ popStack) id none frame
          ((SparseFrontierProgram.state v p flag [] saved
            (true :: (Encoding.frame body ++ pending)) []).withPC
              (some SparseFrontierProgram.popIfPresentProgram.entry))) c →
      ∀ i, (c.stacks i).length ≤ storageBound bodyBound depth thresholdBound n := by
  have hlocal : ∀ t c, t ≤ 9 * body.length + 11 →
      Trace SparseFrontierProgram.popIfPresentProgram t
        ((SparseFrontierProgram.state v p flag [] saved
          (true :: (Encoding.frame body ++ pending)) []).withPC
            (some SparseFrontierProgram.popIfPresentProgram.entry)) c →
      ∀ i, (c.stacks i).length ≤ storageBound bodyBound depth thresholdBound n := by
    intro t c ht hc i
    have hbits := SparseFrontierProgram.popIfPresent_prefix_space body saved pending
      v p flag t c ht hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    unfold storageBound
    omega
  simpa only [max_self] using StructuredSpace.liftProgram_stack_bound
    SparseFrontierProgram.popIfPresentProgram register (ambient ∘ popStack) frame
    register.injective (ambient.injective.comp popStack.injective)
    (SparseFrontierProgram.popIfPresent_cons_trace body saved pending v p flag) hlocal hframe

/-- Both framed children are present at entry. The existing concrete pair
copy consumes each child; its prefix bound includes both copies and scratch. -/
theorem pair_lifted_space {R S : ℕ} (register : Fin 4 ↪ Fin R)
    (ambient : Fin 31 ↪ Fin S)
    (frame : Cfg R S (size SparseFrontierProgram.pushPair + 1))
    (left right saved pending : List Bool) (terminal v p flag : Bool)
    (bodyBound depth thresholdBound n : ℕ)
    (hleft : left.length ≤ bodyBound) (hright : right.length ≤ bodyBound)
    (hsaved : saved.length ≤ n + 1)
    (hpending : pending.length ≤ frontierBound bodyBound depth)
    (hframe : ∀ i, (frame.stacks i).length ≤
      storageBound bodyBound depth thresholdBound n) :
    ∀ prefixSteps c, prefixSteps ≤ 13 * right.length + 13 * left.length + 37 →
      Trace (ProgramLinking.liftProgram SparseFrontierProgram.pushPairProgram
        register (ambient ∘ pairStack)) prefixSteps
        (ProgramLinking.embedCfg register (ambient ∘ pairStack) id none frame
          ((ExecWorklistProgram.data terminal v p flag pending saved
            (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
              (some SparseFrontierProgram.pushPairProgram.entry))) c →
      ∀ i, (c.stacks i).length ≤ storageBound bodyBound depth thresholdBound n := by
  have hlocal : ∀ t c, t ≤ 13 * right.length + 13 * left.length + 37 →
      Trace SparseFrontierProgram.pushPairProgram t
        ((ExecWorklistProgram.data terminal v p flag pending saved
          (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
            (some SparseFrontierProgram.pushPairProgram.entry)) c →
      ∀ i, (c.stacks i).length ≤ storageBound bodyBound depth thresholdBound n := by
    intro t c ht hc i
    have hbits := SparseFrontierProgram.pushPair_prefix_space left right saved pending
      terminal v p flag t c ht hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    unfold storageBound
    omega
  simpa only [max_self] using StructuredSpace.liftProgram_stack_bound
    SparseFrontierProgram.pushPairProgram register (ambient ∘ pairStack) frame
    register.injective (ambient.injective.comp pairStack.injective)
    (SparseFrontierProgram.pushPair_trace left right saved pending terminal v p flag)
    hlocal hframe

/-- One concrete accumulator call returns the canonical new total and clears
both temporary ports. Its prefix bound is uniform across all visited leaves. -/
theorem count_lifted_execution {R S : ℕ} (register : Fin 8 ↪ Fin R)
    (ambient : Fin 31 ↪ Fin S)
    (frame : Cfg R S (size SparseCountProgram.Accumulator.command + 1))
    (regs : Fin 8 → Bool) (a b n bodyBound depth thresholdBound : ℕ)
    (hcount : a + b ≤ 2 ^ n)
    (hframe : ∀ i, (frame.stacks i).length ≤
      storageBound bodyBound depth thresholdBound n) :
    ∃ (t : ℕ) (final : StructuredProgram.State 8 3),
      t ≤ 100 * (n + 1) ∧
      Trace (ProgramLinking.liftProgram SparseCountProgram.Accumulator.program
        register (ambient ∘ countStack)) t
        (ProgramLinking.embedCfg register (ambient ∘ countStack) id none frame
          ((SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b)).withPC
            (some SparseCountProgram.Accumulator.program.entry)))
        (ProgramLinking.embedCfg register (ambient ∘ countStack) id none frame
          (final.withPC none)) ∧
      final.stacks 0 = binaryNat (a + b) ∧ final.stacks 1 = [] ∧ final.stacks 2 = [] ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (ProgramLinking.liftProgram SparseCountProgram.Accumulator.program
          register (ambient ∘ countStack)) prefixSteps
          (ProgramLinking.embedCfg register (ambient ∘ countStack) id none frame
            ((SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b)).withPC
              (some SparseCountProgram.Accumulator.program.entry))) c →
        ∀ i, (c.stacks i).length ≤ storageBound bodyBound depth thresholdBound n := by
  obtain ⟨t, final, ht, htrace, houtput, hclear1, hclear2, hprefix⟩ :=
    SparseCountProgram.Accumulator.canonical_execution regs a b n hcount
  have hlocal : ∀ prefixSteps c, prefixSteps ≤ t →
      Trace SparseCountProgram.Accumulator.program prefixSteps
        ((SparseCountProgram.Accumulator.state regs (binaryNat a) (binaryNat b)).withPC
          (some SparseCountProgram.Accumulator.program.entry)) c →
      ∀ i, (c.stacks i).length ≤ storageBound bodyBound depth thresholdBound n := by
    intro prefixSteps c hle hc i
    have hbits := hprefix prefixSteps c hle hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    unfold storageBound
    omega
  refine ⟨t, final, ht, ?_, houtput, hclear1, hclear2, ?_⟩
  · exact ProgramLinking.relocate_trace SparseCountProgram.Accumulator.program _
      register (ambient ∘ countStack) id none frame register.injective
      (ambient.injective.comp countStack.injective) (fun _ => rfl) htrace
  · simpa only [max_self] using StructuredSpace.liftProgram_stack_bound
      SparseCountProgram.Accumulator.program register (ambient ∘ countStack) frame
      register.injective (ambient.injective.comp countStack.injective) htrace hlocal hframe

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
