import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCount
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

/-- Each fixed-high query counts free assignments without pruning original
clause violations; its optional marked violation is part of the source test. -/
theorem residual_count_le {n : ℕ} (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) :
    NodeSemantics.ternaryFixedHighCount H high hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : ResidualEmbedding.Free H → Bool, 1 :=
      Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = 2 ^ (n-H.card) := by simp [ResidualEmbedding.Free]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

/-- The rank function is the original source function in descending high-ID
order. Out-of-range proof indices contribute zero. -/
theorem rank_value_le {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) :
    rankValue H hashes marked clause rank ≤ 2 ^ n := by
  unfold rankValue
  split_ifs
  · exact residual_count_le H _ hashes marked clause
  · exact Nat.zero_le _

theorem full_count_le {n : ℕ} (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    fullCount hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : Fin n → Bool, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

/-- This is a mathematical prefix sum only. The machine retains a binary
accumulator and odometer, never this exponential range as a list. -/
theorem rank_prefix_le {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank ≤ 2 ^ H.card) :
    rankSum (rankValue H hashes marked clause) 0 rank ≤ 2 ^ n := by
  have hs : List.Sublist (List.range' 0 rank) (List.range' 0 (2 ^ H.card)) :=
    List.range'_sublist_right.mpr hr
  have hb := (hs.map (rankValue H hashes marked clause)).sum_le_sum
    (fun _ _ => Nat.zero_le _)
  change rankSum (rankValue H hashes marked clause) 0 rank ≤
    rankSum (rankValue H hashes marked clause) 0 (2 ^ H.card) at hb
  rw [rankSum_fullCount] at hb
  exact hb.trans (full_count_le hashes marked clause)

/-- Appending the current residual count advances exactly one rank. -/
theorem rank_prefix_succ (value : ℕ → ℕ) (rank : ℕ) :
    rankSum value 0 rank + value rank = rankSum value 0 (rank+1) := by
  unfold rankSum
  rw [←List.range'_append_1 (s:=0) (m:=rank) (n:=1)]
  simp

/-- Every instruction and compiled prefix of the fixed stream leaves the
whole durable selector/high-counter interval unchanged. -/
theorem stream_durable_frame {a b : Data} {steps : ℕ}
    (he : Eval QueryStreamProgram.command steps a b)
    (i : Fin 896) (hi : 768 ≤ i.val ∧ i.val ≤ 831) : b.stacks i = a.stacks i := by
  let H := fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831
  have hs := eval_rebase H QuerySelectorFrames.command_avoids he (fun _ => [])
  exact CommandStackTransport.eval_shadow_prefix_frame H QuerySelectorFrames.command_avoids
    330 323 hs (by omega) (compiled_halt_trace he 330 323) i hi

/-- The paid counter copy and real guard restoration preserve the live
accumulator, durable odometer, and both adder/counter scratch words. -/
theorem conditioned_durable_frame {a b : Data} {steps : ℕ}
    (he : Eval QueryStreamProgram.command steps (copiedHighCounter a) b)
    (i : Fin 896) (hi : i ∈ ([788,789,790,791] : List (Fin 896))) :
    (⟨Function.update b.regs 21 true,b.stacks⟩ : Data).stacks i = a.stacks i := by
  change b.stacks i = a.stacks i
  have hr : 768 ≤ i.val ∧ i.val ≤ 831 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  rw [stream_durable_frame he i hr]
  apply copiedHighCounter_frame
  · intro h
    subst i
    simp at hi
  · intro h
    subst i
    simp at hi

/-- The physical decoder at the beginning of this fixed stream sees exactly
the original descending high-coordinate rank, returned in ascending ambient
order. No arbitrary reindexing is supplied. -/
theorem decoded_rank {n : ℕ} (H : Finset (Fin n)) (a : Data)
    (words : List (List Bool)) (rf : Fin 4 → Bool)
    (hshape : words.map List.length = List.replicate H.card 1)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (rank : Fin (2 ^ H.card)) (hr : CounterPrograms.value words.flatten = rank.val) :
    (highResult (resetHighState (copiedHighCounter a)) rf words.flatten).stacks 703 =
      List.ofFn (HighIncidence.glue H
        (SqrtLog.HighIncidenceProgram.Rank.highEquiv
          (SqrtLog.HighIncidenceProgram.Order.highOrder H) rank) (fun _ => false)) := by
  rw [preparedBranch_high,hm]
  exact HighBranchSpace.rank_high_vector_semantics H words hshape rank hr

/-- The genuine binary adder consumes a canonical residual answer, retaining
at most ambient n+1 bits even after exponentially many preceding branches. -/
theorem add_rank {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
    (a : Data) (hacc : BinaryArithmetic.toNat (a.stacks 788) =
      rankSum (rankValue H hashes marked clause) 0 rank)
    (hlen : (a.stacks 788).length ≤ n+1)
    (hnext : a.stacks 323 = countWord (rankValue H hashes marked clause rank))
    (hscratch : a.stacks 791 = []) :
    ∃ steps rf, steps ≤ 16*(n+2)+3 ∧
      let b := Mass.state highPorts.mass a rf
        (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []
      Eval (Mass.invoke highPorts.mass) steps a b ∧
      b.stacks 323 = [] ∧ b.stacks 791 = [] ∧
      (b.stacks 788).length ≤ n+1 ∧
      BinaryArithmetic.toNat (b.stacks 788) =
        rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
      (∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → b.stacks i = a.stacks i) := by
  have hv : BinaryArithmetic.toNat (a.stacks 788) + BinaryArithmetic.toNat (a.stacks 323) =
      rankSum (rankValue H hashes marked clause) 0 (rank+1) := by
    rw [hacc,hnext,countWord_toNat,rank_prefix_succ]
  have hn : (a.stacks 323).length ≤ n+1 := by
    rw [hnext]
    exact countWord_length_le (rank_value_le H hashes marked clause rank)
  have hp : BinaryArithmetic.toNat (a.stacks 788) + BinaryArithmetic.toNat (a.stacks 323) <
      2 ^ (n+1) := by
    rw [hv]
    exact (rank_prefix_le H hashes marked clause (rank+1) (by omega)).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨steps,ht,rf,he⟩ := Mass.invoke_eval highPorts.mass a
    (fun i => a.regs (highPorts.mass.register i)) (a.stacks 788) (a.stacks 323)
  have hself : Mass.state highPorts.mass a (fun i => a.regs (highPorts.mass.register i))
      (a.stacks 788) (a.stacks 323) = a := mass_self highPorts a hscratch
  rw [hself] at he
  have hout : (Mass.state highPorts.mass a rf
      (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []).stacks 788 =
        BinaryArithmetic.add (a.stacks 788) (a.stacks 323) := mass_stack highPorts a rf _ [] 0
  refine ⟨steps,rf,?_,he,mass_stack highPorts a rf _ [] 1,
    mass_stack highPorts a rf _ [] 2,?_,?_,?_⟩
  · have hm : max (a.stacks 788).length (a.stacks 323).length ≤ n+1 := max_le hlen hn
    omega
  · rw [hout]
    exact HighIncidenceStream.length_add_of_lt (n+1) _ _ hlen hn hp
  · rw [hout,BinaryArithmetic.toNat_add,hv]
  · intro i hi hj hk
    apply mass_frame highPorts a rf _ [] i
    intro j
    fin_cases j <;> simp [highPorts,Ne.symm hi,Ne.symm hj,Ne.symm hk]

/-- Exact off-port frame plus the preceding numerical width proof restores a
fixed compact boundary after every real native addition. -/
theorem mass_boundary (a : Data) (rf : Fin 8 → Bool) (acc : List Bool) (B : ℕ)
    (hacc : acc.length ≤ B)
    (hframe : ∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → (a.stacks i).length ≤ B) :
    ∀ i, ((Mass.state highPorts.mass a rf acc []).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = 788
  · subst i
    exact (congrArg List.length (mass_stack highPorts a rf acc [] 0)).le.trans hacc
  · by_cases hj : i = 323
    · subst i
      have he : (Mass.state highPorts.mass a rf acc []).stacks 323 = [] :=
        mass_stack highPorts a rf acc [] 1
      rw [he]
      exact Nat.zero_le _
    · by_cases hk : i = 791
      · subst i
        have he : (Mass.state highPorts.mass a rf acc []).stacks 791 = [] :=
          mass_stack highPorts a rf acc [] 2
        rw [he]
        exact Nat.zero_le _
      · rw [mass_frame highPorts a rf acc [] i (by
          intro j
          fin_cases j <;> simp [highPorts,Ne.symm hi,Ne.symm hj,Ne.symm hk])]
        exact hframe i hi hj hk

/-- The native adder's three local words have a fixed polynomial prefix cap.
Arbitrarily retained caller words enter only through the outside maximum. -/
theorem mass_prefix_at (a b : Data) (steps width B : ℕ) (input output : Fin 896)
    (he : Eval (Mass.invoke highPorts.mass) steps a b)
    (hacc : (a.stacks 788).length ≤ width) (hnext : (a.stacks 323).length ≤ width)
    (hscratch : a.stacks 791 = []) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∀ t z, t ≤ steps+1 → Trace (compiled (Mass.invoke highPorts.mass) input output) t
      (a.withPC (some (compiled (Mass.invoke highPorts.mass) input output).entry)) z →
      ∀ i, (z.stacks i).length ≤ max (20*(width+1)) B := by
  let regs := fun i => a.regs (highPorts.mass.register i)
  let localStart := Mass.data regs (a.stacks 788) (a.stacks 323)
  have hproject : projectState highPorts.mass.register highPorts.mass.stack a = localStart := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [highPorts, BinaryPrograms.Add.stackState, hscratch]
  obtain ⟨localSteps,hsteps,rf,ht⟩ := Mass.program_trace regs (a.stacks 788) (a.stacks 323)
  have htime : localSteps ≤ 16*(width+1)+2 := by
    have hm := max_le hacc hnext
    omega
  have hi : dataBits (localStart.withPC (some Mass.program.entry)) ≤ 3*width := by
    apply StreamResources.dataBits_le_mul
    intro i
    fin_cases i <;> simp [localStart, Mass.data, BinaryPrograms.Add.stackState, hacc, hnext]
  have hlocal : ∀ t z, t ≤ localSteps → Trace Mass.program t
      (localStart.withPC (some Mass.program.entry)) z →
      ∀ i, (z.stacks i).length ≤ max (20*(width+1)) B := by
    intro t z htle hz i
    have hb := StructuredSpace.local_stack_bound Mass.program
      (steps:=16*(width+1)+2) hi t z (htle.trans htime) hz i
    exact hb.trans ((show 3*width+(16*(width+1)+2) ≤ 20*(width+1) by omega).trans
      (Nat.le_max_left _ _))
  have hlocalTrace : Trace Mass.program localSteps
      ((projectState highPorts.mass.register highPorts.mass.stack a).withPC
        (some Mass.program.entry))
      ((Mass.data rf (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []).withPC none) := by
    rw [hproject]
    exact ht
  have hcall := eval_call_from_state Mass.program highPorts.mass.register highPorts.mass.stack a
    highPorts.mass.register_injective highPorts.mass.stack_injective hlocalTrace
  have hp := HighQuerySpace.lifted_call_bound Mass.program highPorts.mass.register
    highPorts.mass.stack highPorts.mass.register_injective highPorts.mass.stack_injective
    a localStart _ hproject localSteps (max (20*(width+1)) B) ht hlocal
    (fun i => (hB i).trans (Nat.le_max_right _ _)) input output
  have hsame : steps = localSteps := StreamResources.eval_steps_eq input output he hcall
  simpa only [hsame] using StructuredSpace.compiled_halt_stack_bound hcall input output hp

/-- The canonical public metadata selects the accumulator and residual word. -/
theorem mass_prefix (a b : Data) (steps width B : ℕ)
    (he : Eval (Mass.invoke highPorts.mass) steps a b)
    (hacc : (a.stacks 788).length ≤ width) (hnext : (a.stacks 323).length ≤ width)
    (hscratch : a.stacks 791 = []) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∀ t z, t ≤ steps+1 → Trace (compiled (Mass.invoke highPorts.mass) 788 323) t
      (a.withPC (some (compiled (Mass.invoke highPorts.mass) 788 323).entry)) z →
      ∀ i, (z.stacks i).length ≤ max (20*(width+1)) B :=
  mass_prefix_at a b steps width B 788 323 he hacc hnext hscratch hB

open HashGreedyProgram.NativeRound

/-- This composes one actual fixed conditioned-stream execution with its paid
counter copy, guard restoration and native addition. The exact stream answer
is still an explicit per-run fact to be supplied by the stream proof. The
compact endpoint bound is independent of the transient prefix envelope. -/
theorem branch_step_resources {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
    (a middle : Data) (querySteps L B D K : ℕ)
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hs : StageSpace QueryStreamProgram.command querySteps (copiedHighCounter a) K)
    (hacc : BinaryArithmetic.toNat (a.stacks 788) =
      rankSum (rankValue H hashes marked clause) 0 rank)
    (hlen : (a.stacks 788).length ≤ n+1)
    (hnext : middle.stacks 323 = countWord (rankValue H hashes marked clause rank))
    (htmp : a.stacks 791 = [])
    (hD : ∀ i, (a.stacks i).length ≤ D)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L)
    (hwidth : n+1 ≤ B)
    (hboundary : ∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → (middle.stacks i).length ≤ B) :
    ∃ steps b, Eval HighQueryProgram.branch steps a b ∧
      steps ≤ querySteps + 11*L + 16*(n+2) + 15 ∧
      BinaryArithmetic.toNat (b.stacks 788) =
        rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
      (b.stacks 788).length ≤ n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
      b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
      b.regs 21=true ∧ (∀ i, (b.stacks i).length ≤ B) ∧
      StageSpace HighQueryProgram.branch (steps+1) a (max (max D K) (20*(n+2))) := by
  let c : Data := ⟨Function.update middle.regs 21 true,middle.stacks⟩
  have hcacc : c.stacks 788=a.stacks 788 := conditioned_durable_frame he 788 (by simp)
  have hctmp : c.stacks 791=[] := (conditioned_durable_frame he 791 (by simp)).trans htmp
  have hclen : (c.stacks 788).length ≤ n+1 := by rw [hcacc]; exact hlen
  have hcnext : c.stacks 323=countWord (rankValue H hashes marked clause rank) := hnext
  obtain ⟨addSteps,rf,haddTime,hadd,hzero,htemp,houtlen,hvalue,hframe⟩ :=
    add_rank H hashes marked clause rank hr c (by rw [hcacc]; exact hacc) hclen hcnext hctmp
  let b := Mass.state highPorts.mass c rf
    (BinaryArithmetic.add (c.stacks 788) (c.stacks 323)) []
  obtain ⟨hconditioned,hconditionedTime,hconditionedSpace⟩ :=
    HighQueryProgram.conditioned_resources a middle querySteps L D K he hs hD h330 h792 h789
  have hcb : ∀ i, (c.stacks i).length ≤ max D K := by
    intro i
    exact hconditionedSpace.bound _ _ (Nat.le_succ _)
      (compiled_trace hconditioned 778 777) i
  have hcwidth : (c.stacks 323).length ≤ n+1 := by
    rw [hcnext]
    exact countWord_length_le (rank_value_le H hashes marked clause rank)
  have hmassSpace : StageSpace (Mass.invoke highPorts.mass) addSteps c
      (max (max D K) (20*(n+2))) := by
    constructor
    intro t z ht hz i
    have hb := mass_prefix_at c b addSteps (n+1) (max D K) 778 777 hadd
      hclen hcwidth hctmp hcb t z (ht.trans (Nat.le_succ _)) hz i
    simpa only [Nat.add_assoc,Nat.max_comm] using hb
  have hcondSpace : StageSpace HighQueryProgram.conditioned (copyHighCost a+(querySteps+1)) a
      (max (max D K) (20*(n+2))) :=
    ⟨fun t z ht hz i => (hconditionedSpace.bound t z (ht.trans (Nat.le_succ _)) hz i).trans
      (Nat.le_max_left _ _)⟩
  have hwhole : Eval HighQueryProgram.branch (copyHighCost a+(querySteps+1)+addSteps) a b :=
    hconditioned.seq hadd
  have hwholeSpace := StageSpace.seq hconditioned hadd hcondSpace hmassSpace
  refine ⟨_,b,hwhole,by omega,hvalue,houtlen,hzero,htemp,?_,?_,?_,?_,?_⟩
  · exact (hframe 789 (by decide) (by decide) (by decide)).trans
      (conditioned_durable_frame he 789 (by simp))
  · exact (hframe 790 (by decide) (by decide) (by decide)).trans
      (conditioned_durable_frame he 790 (by simp))
  · change (Mass.state highPorts.mass c rf _ []).regs 21=true
    unfold Mass.state
    rw [embedState_register_frame]
    · simp [c]
    · rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      simp only [highPorts, Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
      have hlt := i.isLt
      omega
  · intro i
    by_cases hi : i=788
    · subst i
      exact houtlen.trans hwidth
    · by_cases hj : i=323
      · subst i
        rw [show b.stacks 323=[] from hzero]
        exact Nat.zero_le _
      · by_cases hk : i=791
        · subst i
          rw [show b.stacks 791=[] from htemp]
          exact Nat.zero_le _
        · rw [hframe i hi hj hk]
          exact hboundary i hi hj hk
  · exact ⟨StructuredSpace.compiled_halt_stack_bound hwhole 778 777 hwholeSpace.bound⟩

/-- A complete current high tuple has linear physical length, even when its
numeric value is exponentially large. -/
theorem counter_length {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) :
    (Encoding.encodeList id words).length=4*H.card+1 := by
  rw [Enumerators.encoded_shape_length hshape]
  simp
  omega

/-- One real odometer step restores the same compact boundary. -/
theorem advance_boundary {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) (a : Data) (B : ℕ)
    (hwidth : 4*H.card+1 ≤ B) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((ExecCNFTupleEnumeration.advanceResult highPorts.counter a words).stacks i).length ≤ B := by
  intro i
  by_cases hc : i=789
  · subst i
    rw [show (789 : Fin 896)=highPorts.counter.counter from rfl,
      ExecCNFTupleEnumeration.advanceResult_counter,
      ExecCNFTupleEnumeration.bumpWords_encoded_length,counter_length H words hshape]
    exact hwidth
  · by_cases hs : i=790
    · subst i
      rw [show (790 : Fin 896)=highPorts.counter.scratch from rfl,
        ExecCNFTupleEnumeration.advanceResult_scratch]
      exact Nat.zero_le _
    · rw [←ExecCNFTupleEnumeration.advanceResult_outside highPorts.counter a words i hc hs]
      exact hB i

/-- The actual high odometer has only two local stack words. Its complete
prefix bound is a maximum with retained storage; the number of high assignments
never enters this local space estimate. -/
theorem advance_resources {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) (a : Data) (B : ℕ)
    (hc : a.stacks 789=Encoding.encodeList id words) (hs : a.stacks 790=[])
    (hwidth : 4*H.card+1 ≤ B) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps, steps ≤ 28*H.card+11 ∧
      Eval (ExecCNFTupleEnumeration.advanceCmd highPorts.counter) steps a
        (ExecCNFTupleEnumeration.advanceResult highPorts.counter a words) ∧
      (∀ i, ((ExecCNFTupleEnumeration.advanceResult highPorts.counter a words).stacks i).length ≤ B) ∧
      StageSpace (ExecCNFTupleEnumeration.advanceCmd highPorts.counter) (steps+1) a
        (max (40*(H.card+1)) B) := by
  let p := highPorts.counter
  let localStart := CounterForPrograms.localData (a.regs (p.register 0))
    (a.regs (p.register 1)) (a.regs (p.register 2)) (Encoding.encodeList id words) []
  have hproject : projectState p.register (CounterForPrograms.stackPorts p) a = localStart := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [CounterForPrograms.stackPorts, p, highPorts, hc, hs]
  obtain ⟨incSteps,hincTime,ht⟩ := ExecCNFTupleOdometer.increment_runs words []
    (a.regs (p.register 0)) (a.regs (p.register 1)) (a.regs (p.register 2))
  have hlocalTrace : Trace ExecCNFTupleOdometer.program incSteps
      (localStart.withPC (some ExecCNFTupleOdometer.program.entry))
      ((CounterForPrograms.localData false false (ExecCNFTupleOdometer.bumpWords words).1
        (Encoding.encodeList id (ExecCNFTupleOdometer.bumpWords words).2) []).withPC none) := by
    simpa [ExecCNFTupleOdometer.cfg,CounterForPrograms.localData,
      StructuredProgram.State.withPC,localStart] using ht
  have hlocalSize : dataBits (localStart.withPC (some ExecCNFTupleOdometer.program.entry)) ≤
      2*(4*H.card+1) := by
    apply StreamResources.dataBits_le_mul
    intro i
    fin_cases i <;> simp [localStart, CounterForPrograms.localData,
      counter_length H words hshape]
  have hincTime' : incSteps ≤ 28*H.card+10 := by
    rw [counter_length H words hshape] at hincTime
    omega
  have hlocal : ∀ t z, t ≤ incSteps → Trace ExecCNFTupleOdometer.program t
      (localStart.withPC (some ExecCNFTupleOdometer.program.entry)) z →
      ∀ i, (z.stacks i).length ≤ max (40*(H.card+1)) B := by
    intro t z htle hz i
    have hb := StructuredSpace.local_stack_bound ExecCNFTupleOdometer.program
      (steps:=28*H.card+10) hlocalSize t z (htle.trans hincTime') hz i
    exact hb.trans ((show 2*(4*H.card+1)+(28*H.card+10) ≤ 40*(H.card+1) by omega).trans
      (Nat.le_max_left _ _))
  have hp := HighQuerySpace.lifted_call_bound ExecCNFTupleOdometer.program p.register
    (CounterForPrograms.stackPorts p) p.register.injective
    (CounterForPrograms.stackPorts p).injective a localStart _ hproject incSteps
    (max (40*(H.card+1)) B) hlocalTrace hlocal
    (fun i => (hB i).trans (Nat.le_max_right _ _)) 778 777
  obtain ⟨actualInc,hactualTime,hi⟩ := ExecCNFTupleEnumeration.increment_eval p words a hc hs
  have hcall := eval_call_from_state ExecCNFTupleOdometer.program p.register
    (CounterForPrograms.stackPorts p) a p.register.injective
    (CounterForPrograms.stackPorts p).injective (by rw [hproject]; exact hlocalTrace)
  have hsame : actualInc=incSteps := StreamResources.eval_steps_eq 778 777 hi hcall
  have hincSpace : StageSpace (ExecCNFTupleEnumeration.incrementCmd p) actualInc a
      (max (40*(H.card+1)) B) := by
    constructor
    simpa only [hsame] using hp
  have hnot : Eval (.base (.atom (.bnot (p.register 2) (p.register 2)))) 1
      (ExecCNFTupleEnumeration.incrementResult p a words)
      (ExecCNFTupleEnumeration.advanceResult p a words) := .base (.atom _ _)
  have hnotSpace : StageSpace (.base (.atom (.bnot (p.register 2) (p.register 2)))) 1
      (ExecCNFTupleEnumeration.incrementResult p a words) (max (40*(H.card+1)) B) := by
    constructor
    intro t z htle hz i
    have hbound : ((ExecCNFTupleEnumeration.incrementResult p a words).stacks i).length ≤ B :=
      advance_boundary H words hshape a B hwidth hB i
    have ht : t=0 ∨ t=1 := by omega
    rcases ht with rfl|rfl
    · cases hz
      exact hbound.trans (Nat.le_max_right _ _)
    · rw [trace_same_length_unique hz (compiled_trace hnot 778 777)]
      exact hbound.trans (Nat.le_max_right _ _)
  have he := hi.seq hnot
  have hprefix := StageSpace.seq hi hnot hincSpace hnotSpace
  refine ⟨actualInc+1,by omega,he,advance_boundary H words hshape a B hwidth hB,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hprefix.bound⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
