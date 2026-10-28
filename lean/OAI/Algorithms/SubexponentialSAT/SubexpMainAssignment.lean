import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAssignmentStaging
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssignmentPorts

namespace OAI.Algorithms

/-! Actual assignment construction in the Main storage convention.

Binary r/Q/delta/D are copied from persistent 21/17/16/19; scopes are read
from layout master 640. The computed assignment, framed alphabet, and word
width are retained on 642/643/644. Canonical unary r/Q/delta/D are copied to
645..648 before assignment consumes them. Ordinary stacks 0..50 are cleared
and the source ring bank 128..137 is framed throughout. -/

namespace SubexponentialSAT.SubexpMainAssignment

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

noncomputable def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 63
  labels := size SubexpAssignmentStaging.command + 1
  program := SubexpAssignmentStaging.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

noncomputable def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q)) : Prop where
  wordOrder : (first :: tail).map ReadPlan.encodeWord = AssignmentAlphabetSemantics.wordBytes r Q
  assignment : b.stacks (master alloc 2) = SubexpAssignmentStaging.assignedBytes Δ D scopes hd first tail
  alphabet : b.stacks (master alloc 3) =
    ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)
  width : (b.stacks (master alloc 4)).length = Q * r
  inputs : ∀ i, b.stacks (inputPort alloc i) = a.stacks (inputPort alloc i)
  headers : ∀ i, b.stacks (master alloc (headerIndex i)) =
    List.replicate ((![r, Q, Δ, D] : Fin 4 → ℕ) i) true
  scratch : ∀ i, b.stacks (lowPort alloc i) = []
  frame : ∀ j, (¬ ∃ i, stackMap alloc i = j) → b.stacks j = a.stacks j
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) → b.regs i = a.regs i
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpAssignmentStaging.Data) (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (hr : SubexpAssignmentStaging.Result ((procedure er alloc).project a) out
      r Q Δ D scopes hd first tail) :
    Result alloc a ((procedure er alloc).install a out) r Q Δ D scopes hd first tail := by
  have hs (i : Fin 63) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a out (procedure er alloc).stack.injective i
  have ho (i : Fin 3) : ((procedure er alloc).install a out).stacks (master alloc (targetIndex i)) =
      out.stacks (SubexpAssignmentStaging.outputTarget i) := by
    have h := hs (SubexpAssignmentStaging.outputTarget i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at h
    simpa only [stackMap_output] using h
  constructor
  · exact hr.wordOrder
  · exact (ho 0).trans hr.assignment
  · exact (ho 1).trans hr.alphabet
  · exact (congrArg List.length (ho 2)).trans hr.width
  · intro i
    have h := hs (SubexpAssignmentStaging.input i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at h
    rw [stackMap_input, hr.inputs] at h
    change ((procedure er alloc).install a out).stacks (inputPort alloc i) =
      a.stacks (stackMap alloc (SubexpAssignmentStaging.input i)) at h
    simpa only [stackMap_input] using h
  · intro i
    have h := hs (SubexpAssignmentStaging.headerTarget i)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at h
    rw [stackMap_header] at h
    exact h.trans (hr.headers i)
  · intro i
    have h := hs (i.castAdd 12)
    change ((procedure er alloc).install a out).stacks (stackMap alloc _) = _ at h
    rw [stackMap_low] at h
    exact h.trans (hr.scratch _ i.isLt)
  · intro i hi; exact embedState_stack_frame _ _ _ _ _ hi
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans (hr.registers i)
  · intro i hi; exact embedState_register_frame _ _ _ _ _ hi
  · exact Procedure.install_control _ _ _

namespace Result

theorem persistent_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    (h : Result alloc a b r Q Δ D scopes hd first tail) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  by_cases hi : ∃ j : Fin 4, metadataIndex j = i
  · obtain ⟨j, rfl⟩ := hi
    have hh := h.inputs ⟨j.val, by omega⟩
    simpa only [inputPort, Fin.val_mk, dite_eq_left j.isLt] using hh
  · apply h.frame
    rintro ⟨j, hj⟩
    by_cases hlow : j.val < 51
    · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
      have hn := alloc.enough.trans alloc.within
      simp only [stackMap, dite_eq_left hlow, lowPort, ordinary, persistent,
        Fin.val_natAdd] at hv
      omega
    by_cases hmid : j.val < 55
    · apply hi
      refine ⟨⟨j.val - 51, by omega⟩, ?_⟩
      exact persistent_injective es (by
        simpa only [stackMap, dite_eq_right hlow, dite_eq_left hmid] using hj)
    · exact SubexpLayoutPorts.master_ne_persistent alloc
        (masterIndex ⟨j.val - 55, by omega⟩) i (by
          simpa only [stackMap, dite_eq_right hlow, dite_eq_right hmid] using hj)

theorem master_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    (h : Result alloc a b r Q Δ D scopes hd first tail) (i : Fin 32)
    (hi : i ∉ writtenMasters) : b.stacks (master alloc i) = a.stacks (master alloc i) := by
  by_cases h0 : i = 0
  · subst i
    exact h.inputs 4
  · exact h.frame _ (stackMap_avoids_master alloc i h0 hi)

theorem source_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    (h : Result alloc a b r Q Δ D scopes hd first tail) (i : Fin 10) :
    b.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  exact h.frame _ (stackMap_avoids_middle alloc _
    (by simp only [ordinary]; omega) (by simp only [ordinary]; omega))

theorem work_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    (h : Result alloc a b r Q Δ D scopes hd first tail) (j : Fin (totalStacks es))
    (hlo : 51 ≤ j.val) (hhi : j.val < 640) : b.stacks j = a.stacks j :=
  h.frame _ (stackMap_avoids_middle alloc j hlo hhi)

theorem threshold_frame {er es : ℕ} {alloc : Allocation es} {a b : MainState er es}
    {r Q Δ D : ℕ} {scopes : List (List ℕ)}
    {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
    {first : MulticolorTypes.Word r Q} {tail : List (MulticolorTypes.Word r Q)}
    (h : Result alloc a b r Q Δ D scopes hd first tail) (i : Fin (totalStacks es))
    (hstart : alloc.ordinaryCount ≤ i.val) (hend : i.val < workStacks es) :
    b.stacks i = a.stacks i := by
  apply h.frame
  rintro ⟨j, hj⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  have hn := alloc.enough
  by_cases hlow : j.val < 51
  · simp only [stackMap, dite_eq_left hlow, lowPort, ordinary] at hv
    omega
  by_cases hmid : j.val < 55
  · rw [stackMap_of_middle alloc j hlow hmid] at hj
    have hv := congrArg Fin.val hj
    simp only [persistent, Fin.val_natAdd] at hv
    omega
  · rw [stackMap_of_high alloc j hlow hmid] at hj
    have hv := congrArg Fin.val hj
    simp only [SubexpLayoutPorts.master_val] at hv
    omega

end Result

noncomputable def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (r Q Δ D : ℕ) (scopes : List (List ℕ)) : ℕ :=
  SubexpAssignmentStaging.runtimeBound ((procedure er alloc).project a) r Q Δ D scopes

/-- The only data premises identify the actual metadata and scope bytes.
Assignment, alphabet, and word width are conclusions of execution. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (r Q Δ D : ℕ) [NeZero r] (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (hv : ∀ i, CounterPrograms.value (a.stacks (persistent es (metadataIndex i))) =
      (![r, Q, Δ, D] : Fin 4 → ℕ) i)
    (hs : a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q),
      ∃ n ≤ runtimeBound alloc a r Q Δ D scopes, ∃ b,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b r Q Δ D scopes hd first tail := by
  have hmeta (i : Fin 4) : ((procedure er alloc).project a).stacks (SubexpAssignmentSetup.source i) =
      a.stacks (persistent es (metadataIndex i)) := by
    change a.stacks (stackMap alloc _) = _
    rw [stackMap_metadata]
  have hscope : ((procedure er alloc).project a).stacks (55 : Fin 63) =
      a.stacks (master alloc 0) := rfl
  obtain ⟨first, tail, out, hn, hf, ⟨n, hb, ht⟩, hr⟩ :=
    SubexpAssignmentStaging.run ((procedure er alloc).project a) r Q Δ D scopes hd
      (fun i => by rw [hmeta]; exact hv i) (hscope.trans hs)
  exact ⟨first, tail, n, hb, (procedure er alloc).install a out, hn, hf,
    Procedure.invoke_trace _ _ _ ht, install_result alloc a out r Q Δ D scopes hd first tail hr⟩

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (r Q Δ D : ℕ) [NeZero r] (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (hv : ∀ i, CounterPrograms.value (a.stacks (persistent es (metadataIndex i))) =
      (![r, Q, Δ, D] : Fin 4 → ℕ) i)
    (hs : a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ first : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q), ∃ b,
      (first :: tail).Nodup ∧ (∀ w, w ∈ first :: tail) ∧
      RunsIn (program er alloc) (runtimeBound alloc a r Q Δ D scopes)
        (a.withPC (some (program er alloc).entry)) (b.withPC none) ∧
      Result alloc a b r Q Δ D scopes hd first tail := by
  obtain ⟨first, tail, n, hn, b, hnodup, hfull, heval, hr⟩ := execution alloc a r Q Δ D scopes hd hv hs
  refine ⟨first, tail, b, hnodup, hfull, ⟨n, hn, ?_⟩, hr⟩
  cases heval with
  | call _ ht => exact ht

end SubexponentialSAT.SubexpMainAssignment

end OAI.Algorithms
