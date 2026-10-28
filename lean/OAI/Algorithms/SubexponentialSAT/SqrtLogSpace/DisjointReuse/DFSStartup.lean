import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountDFS

/-! Concrete startup for the shared 80-register, 1220-stack DFS ABI.
The input frame already contains the normalized body and actual parameter words.
This module proves only startup; it does not assume or claim a completed DFS run.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

variable {n : ℕ}

structure Prepared (M : List Bool) (F : RawCNF n) (d : Data) : Prop where
  pending : d.stacks 257 = []
  header : d.stacks 258 = Encoding.encodeNat n
  threshold : d.stacks 259 = M
  total : d.stacks 260 = []
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []
  current : d.stacks 265 = SparseCountProgram.encodeBody F
  low_empty : ∀ i : Fin 1220, i.val < 256 → d.stacks i = []

def startup : Code := .seq startFrontier (.seq startTotal testPending)

theorem startFrontier_refinement (M : List Bool) (F : RawCNF n) (d : Data)
    (hp : Prepared M F d) :
    ∃ e, Eval startFrontier (8 * (SparseCountProgram.encodeBody F).length + 13) d e ∧
      e.stacks 265 = [] ∧
      e.stacks 257 = pendingBytes [⟨F, 0⟩] ∧
      (∀ i, i ≠ 265 → i ≠ 257 → e.stacks i = d.stacks i) := by
  let a := SparseFrontierProgram.state (d.regs 0) (d.regs 1) (d.regs 2)
    (SparseCountProgram.encodeBody F) (Encoding.encodeNat n) [] []
  let b := SparseFrontierProgram.state true false (d.regs 2) [] (Encoding.encodeNat n)
    (Encoding.encodeList id [SparseCountProgram.encodeBody F]) []
  have hin : embedState (registers 3 (by decide)) frontierStack d a = d := by
    apply embedState_eq_of_ports _ _ d d a (registers 3 (by decide)).injective
      frontierStack.injective
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i
      · exact hp.current
      · exact hp.header
      · exact hp.pending
      · exact hp.low_empty 23 (by decide)
    · intro i hi
      rfl
  have he := eval_call_lifted SparseFrontierProgram.initFrontierProgram
    (registers 3 (by decide)) frontierStack d (registers 3 (by decide)).injective
    frontierStack.injective
    (SparseFrontierProgram.initFrontier_trace (SparseCountProgram.encodeBody F)
      (Encoding.encodeNat n) (d.regs 0) (d.regs 1) (d.regs 2))
  change Eval startFrontier _ (embedState _ _ d a) (embedState _ _ d b) at he
  rw [hin] at he
  let e := embedState (registers 3 (by decide)) frontierStack d b
  have hout (i : Fin 4) : e.stacks (frontierStack i) = b.stacks i :=
    embedState_stack _ _ _ _ frontierStack.injective i
  refine ⟨e, he, hout 0, hout 2, ?_⟩
  intro i hc hpending
  by_cases hi : ∃ j, frontierStack j = i
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j
    · exact (hc rfl).elim
    · exact (hout 1).trans hp.header.symm
    · exact (hpending rfl).elim
    · exact (hout 3).trans (hp.low_empty 23 (by decide)).symm
  · exact embedState_stack_frame _ _ _ _ i hi

theorem startup_refinement (M : List Bool) (F : RawCNF n) (d : Data)
    (hp : Prepared M F d) :
    ∃ e, Eval startup (8 * (SparseCountProgram.encodeBody F).length + 16) d e ∧
      Boundary M ⟨[⟨F, 0⟩], 0⟩ e ∧
      (∀ i, i ≠ 257 → i ≠ 260 → i ≠ 265 → e.stacks i = d.stacks i) := by
  obtain ⟨a, ha, hacurrent, hapending, haframe⟩ := startFrontier_refinement M F d hp
  have hatotal : a.stacks 260 = [] := (haframe 260 (by decide) (by decide)).trans hp.total
  let b : Data := ⟨Function.update a.regs 0 false, Function.update a.stacks 260 [false]⟩
  have hb : Eval startTotal 2 a b := startTotal_eval a hatotal
  let e : Data := ⟨readRegs b.regs 2 1 (b.stacks 257).head?, b.stacks⟩
  have he : Eval testPending 1 b e := testPending_eval b
  have hframe (i : Fin 1220) (hi257 : i ≠ 257) (hi260 : i ≠ 260) (hi265 : i ≠ 265) :
      e.stacks i = d.stacks i := by
    change Function.update a.stacks 260 [false] i = d.stacks i
    rw [Function.update_of_ne hi260, haframe i hi265 hi257]
  refine ⟨e, ?_, ?_, hframe⟩
  · exact ha.seq (hb.seq he)
  · constructor
    · simpa only [e, b, Function.update_of_ne (by decide : (257 : Fin 1220) ≠ 260)]
        using hapending
    · exact (hframe 258 (by decide) (by decide) (by decide)).trans hp.header
    · exact (hframe 259 (by decide) (by decide) (by decide)).trans hp.threshold
    · rfl
    · exact (hframe 261 (by decide) (by decide) (by decide)).trans hp.left_empty
    · exact (hframe 262 (by decide) (by decide) (by decide)).trans hp.right_empty
    · exact (hframe 263 (by decide) (by decide) (by decide)).trans hp.leaf_empty
    · simpa only [e, b, Function.update_of_ne (by decide : (265 : Fin 1220) ≠ 260)]
        using hacurrent
    · intro i hi
      rw [hframe i (by intro h; subst i; omega) (by intro h; subst i; omega)
        (by intro h; subst i; omega)]
      exact hp.low_empty i hi
    · simp [e, b, hapending, pendingBytes, Encoding.encodeList, readRegs]

/-- Startup is polynomial-time, so its own local time bounds every source
prefix. This estimate is never applied to the exponentially long DFS loop. -/
theorem startup_prefix_space (d : Data) (bodyLength bound : ℕ)
    (hframe : ∀ i, (d.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 8 * bodyLength + 17 →
      Trace (compiled startup 256 256) prefixSteps
        (d.withPC (some (compiled startup 256 256).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ 1220 * bound + 8 * bodyLength + 17 := by
  have hsum : dataBits (d.withPC (some (compiled startup 256 256).entry)) ≤ 1220 * bound := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 1220))) => hframe i)
    simpa only [dataBits, stackBits, StructuredProgram.State.withPC, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  intro prefixSteps intermediate hle htrace i
  have h := StructuredSpace.local_stack_bound (compiled startup 256 256)
    (steps := 8 * bodyLength + 17) hsum prefixSteps intermediate hle htrace i
  simpa only [Nat.add_assoc] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup
