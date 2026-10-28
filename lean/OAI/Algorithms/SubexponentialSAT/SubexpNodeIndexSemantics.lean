import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentOrder
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexMaster

namespace OAI.Algorithms

/-!
# Exact lookup indices in the physically generated node table

The node order is the tuple machine's actual output order.  Distinctness is
proved from the injective encoding and the residue map, rather than supplied
as a hypothesis about an arbitrary list.  The final command composes the
actual master-table copy with the existing physical search program.
-/

namespace SubexponentialSAT.SubexpNodeIndexSemantics

open BitProgram StructuredCalls
open SubexpNodeMomentOrder (nodeWord)

variable (p μ : ℕ) [Fact p.Prime]
variable (M : SubexpPreparedQuartic.Modulus p 1)

theorem nodeWord_injective (hμ : 0 < μ) : Function.Injective (nodeWord p μ hμ) := by
  intro i j hij
  have hring := SubexpQuarticEncoding.encodeSelected_injective p μ hμ hij
  have hfield := congrArg (SubexpActualRing.rho p μ hμ) hring
  apply (SubexpMachineNodeOrder.nodeEquiv p).injective
  apply Subtype.ext
  simpa only [SubexpActualRing.rho_sectionValue] using hfield

theorem liftedNodeWords_nodup (hμ : 0 < μ) :
    (SubexpNodeLiftData.liftedNodeWords p μ M).Nodup := by
  rw [SubexpNodeMomentOrder.liftedNodeWords_eq p μ M hμ]
  exact List.nodup_ofFn.mpr (nodeWord_injective p μ hμ)

theorem nodeWord_mem (hμ : 0 < μ) (i : Fin (p^4 - 1)) :
    nodeWord p μ hμ i ∈ SubexpNodeLiftData.liftedNodeWords p μ M := by
  rw [SubexpNodeMomentOrder.liftedNodeWords_eq p μ M hμ]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem mem_liftedNodeWords_iff (hμ : 0 < μ) (bits : List Bool) :
    bits ∈ SubexpNodeLiftData.liftedNodeWords p μ M ↔
      ∃ i : Fin (p^4 - 1), nodeWord p μ hμ i = bits := by
  rw [SubexpNodeMomentOrder.liftedNodeWords_eq p μ M hμ]
  exact List.mem_ofFn

theorem getElem_nodeWord (hμ : 0 < μ) (i : Fin (p^4 - 1)) :
    (SubexpNodeLiftData.liftedNodeWords p μ M)[i.val]'(by
      rw [SubexpNodeLiftData.liftedNodeWords_length]
      exact i.isLt) =
      nodeWord p μ hμ i := by
  simpa only [List.get_eq_getElem, nodeWord] using
    SubexpNodeLiftData.liftedNodeWords_get p μ M hμ i

theorem getElem?_nodeWord (hμ : 0 < μ) (i : Fin (p^4 - 1)) :
    (SubexpNodeLiftData.liftedNodeWords p μ M)[i.val]? = some (nodeWord p μ hμ i) := by
  have hi : i.val < (SubexpNodeLiftData.liftedNodeWords p μ M).length := by
    rw [SubexpNodeLiftData.liftedNodeWords_length]
    exact i.isLt
  rw [List.getElem?_eq_getElem hi, getElem_nodeWord p μ M hμ i]

theorem idxOf_nodeWord (hμ : 0 < μ) (i : Fin (p^4 - 1)) :
    (SubexpNodeLiftData.liftedNodeWords p μ M).idxOf (nodeWord p μ hμ i) = i.val := by
  rw [← getElem_nodeWord p μ M hμ i]
  exact SubexpNodeIndexProgram.index_of_getElem _ (liftedNodeWords_nodup p μ M hμ)
    i.val (by
      rw [SubexpNodeLiftData.liftedNodeWords_length]
      exact i.isLt)

/-- Every nonzero field value has its canonical code in this same table. -/
theorem section_code_mem (hμ : 0 < μ) (z : SubexpActualRing.E p) (hz : z ≠ 0) :
    SubexpQuarticEncoding.encodeSelected p μ hμ (SubexpActualRing.sectionValue p μ hμ z) ∈
      SubexpNodeLiftData.liftedNodeWords p μ M := by
  let i := (SubexpMachineNodeOrder.nodeEquiv p).symm ⟨z, hz⟩
  have hi : (SubexpMachineNodeOrder.nodeEquiv p i).val = z :=
    congrArg Subtype.val ((SubexpMachineNodeOrder.nodeEquiv p).apply_symm_apply ⟨z, hz⟩)
  simpa only [nodeWord, hi] using nodeWord_mem p μ M hμ i

theorem idxOf_section_code (hμ : 0 < μ) (z : SubexpActualRing.E p) (hz : z ≠ 0) :
    (SubexpNodeLiftData.liftedNodeWords p μ M).idxOf
        (SubexpQuarticEncoding.encodeSelected p μ hμ (SubexpActualRing.sectionValue p μ hμ z)) =
      ((SubexpMachineNodeOrder.nodeEquiv p).symm ⟨z, hz⟩).val := by
  let i := (SubexpMachineNodeOrder.nodeEquiv p).symm ⟨z, hz⟩
  have hi : (SubexpMachineNodeOrder.nodeEquiv p i).val = z :=
    congrArg Subtype.val ((SubexpMachineNodeOrder.nodeEquiv p).apply_symm_apply ⟨z, hz⟩)
  simpa only [nodeWord, hi] using idxOf_nodeWord p μ M hμ i

/-- Specialization to the actual prime-power precision used by the solver. -/
noncomputable def thetaWord (D : ℕ) (i : Fin (p^4 - 1)) : List Bool :=
  nodeWord p (D+1) (Nat.succ_pos D) i

theorem idxOf_thetaWord (D : ℕ) (i : Fin (p^4 - 1)) :
    (SubexpNodeLiftData.liftedNodeWords p (D+1) M).idxOf (thetaWord p D i) = i.val :=
  idxOf_nodeWord p (D+1) M (Nat.succ_pos D) i

/-- The existing finite search computes the canonical index; no free list,
membership, or distinctness premise remains. -/
theorem command_eval (D : ℕ) (i : Fin (p^4 - 1)) (d : SubexpNodeIndexProgram.Data)
    (hquery : d.stacks 78 = thetaWord p D i)
    (hmaster : d.stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean d) :
    ∃ n ≤ SubexpNodeIndexProgram.budget (thetaWord p D i)
        (SubexpNodeLiftData.liftedNodeWords p (D+1) M), ∃ e : SubexpNodeIndexProgram.Data,
      Eval SubexpNodeIndexProgram.command n d e ∧
      e.stacks = Function.update d.stacks 116 (List.replicate i.val true) ∧
      ∀ j : Fin 16, 5 ≤ j.val → e.regs j = d.regs j := by
  simpa only [idxOf_thetaWord p M D i] using
    SubexpNodeIndexProgram.command_eval d (SubexpNodeLiftData.liftedNodeWords p (D+1) M)
      (thetaWord p D i) hquery hmaster hclean

theorem program_run (D : ℕ) (i : Fin (p^4 - 1)) (d : SubexpNodeIndexProgram.Data)
    (hquery : d.stacks 78 = thetaWord p D i)
    (hmaster : d.stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean d) :
    ∃ e : SubexpNodeIndexProgram.Data,
      RunsIn SubexpNodeIndexProgram.program
        (SubexpNodeIndexProgram.budget (thetaWord p D i)
          (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 1)
        (d.withPC (some SubexpNodeIndexProgram.program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 116 (List.replicate i.val true) ∧
      ∀ j : Fin 16, 5 ≤ j.val → e.regs j = d.regs j := by
  simpa only [idxOf_thetaWord p M D i] using
    SubexpNodeIndexProgram.program_run d (SubexpNodeLiftData.liftedNodeWords p (D+1) M)
      (thetaWord p D i) hquery hmaster hclean

/-- A node delivered by the actual table iterator has a canonical index.
The machine discovers this index from the stored query rather than receiving
it as input. -/
theorem command_eval_of_mem (D : ℕ) (d : SubexpNodeIndexProgram.Data)
    (hquery : d.stacks 78 ∈ SubexpNodeLiftData.liftedNodeWords p (D+1) M)
    (hmaster : d.stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean d) :
    ∃ i : Fin (p^4 - 1), d.stacks 78 = thetaWord p D i ∧
      ∃ n ≤ SubexpNodeIndexProgram.budget (thetaWord p D i)
          (SubexpNodeLiftData.liftedNodeWords p (D+1) M), ∃ e : SubexpNodeIndexProgram.Data,
        Eval SubexpNodeIndexProgram.command n d e ∧
        e.stacks = Function.update d.stacks 116 (List.replicate i.val true) ∧
        ∀ j : Fin 16, 5 ≤ j.val → e.regs j = d.regs j := by
  obtain ⟨i, hi⟩ := (mem_liftedNodeWords_iff p (D+1) M (Nat.succ_pos D) (d.stacks 78)).mp hquery
  exact ⟨i, hi.symm, command_eval p M D i d hi.symm hmaster hclean⟩

abbrev MasterData := StructuredProgram.State 16 320

def localPorts : Fin 256 ↪ Fin 320 := ⟨Fin.castAdd 64, Fin.castAdd_injective _ _⟩

def localState (d : MasterData) : SubexpNodeIndexProgram.Data := projectState id localPorts d

abbrev searchMaster : Cmd 16 320 :=
  liftCommand SubexpNodeIndexProgram.command 78 116 id localPorts

abbrev installAndSearch : Cmd 16 320 := .seq SubexpNodeIndexMaster.command searchMaster

def installedProgram := compiled installAndSearch (300 : Fin 320) 116

theorem clean_after_install (d : MasterData)
    (hc : SubexpNodeIndexProgram.Clean (localState d)) :
    SubexpNodeIndexProgram.Clean (localState (SubexpNodeIndexMaster.result d)) := by
  intro j hj
  have h := hc j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simpa [localState, projectState, localPorts, SubexpNodeIndexMaster.result] using h

/-- The current node is looked up after the real master125 copy from the
generated table300. Both operations have complete measured traces. -/
theorem installAndSearch_eval (D : ℕ) (i : Fin (p^4 - 1)) (d : MasterData)
    (hquery : d.stacks 78 = thetaWord p D i)
    (hmaster : d.stacks 300 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean (localState d)) (htmp : d.stacks 305 = []) :
    ∃ n ≤ SubexpNodeIndexMaster.cost d +
        SubexpNodeIndexProgram.budget (thetaWord p D i)
          (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 1, ∃ e : MasterData,
      Eval installAndSearch n d e ∧
      e.stacks = Function.update (Function.update d.stacks 125 (d.stacks 300))
        116 (List.replicate i.val true) ∧
      ∀ j : Fin 16, 5 ≤ j.val → e.regs j = d.regs j := by
  let before := SubexpNodeIndexMaster.result d
  have hq : (localState before).stacks 78 = thetaWord p D i := by
    simpa [localState, projectState, localPorts, before, SubexpNodeIndexMaster.result] using hquery
  have hm : (localState before).stacks 125 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M) := by
    simpa [localState, projectState, localPorts, before, SubexpNodeIndexMaster.result] using hmaster
  obtain ⟨n, hn, small, he, hs, hr⟩ :=
    command_eval p M D i (localState before) hq hm (clean_after_install d hclean)
  let out := embedState id localPorts before small
  have hsearch : Eval searchMaster (n+1) before out :=
    eval_liftCommand_from_state SubexpNodeIndexProgram.command 78 116 id localPorts before
      Function.injective_id localPorts.injective he
  have hout : out.stacks = Function.update before.stacks 116 (List.replicate i.val true) := by
    change Function.extend localPorts small.stacks before.stacks = _
    rw [hs, ProgramLinking.extend_update localPorts.injective]
    have hbase : Function.extend localPorts (localState before).stacks before.stacks =
        before.stacks :=
      congrArg StructuredProgram.State.stacks
        (embedState_project id localPorts before Function.injective_id localPorts.injective)
    rw [hbase]
    rfl
  refine ⟨SubexpNodeIndexMaster.cost d + (n+1), by omega, out,
    (SubexpNodeIndexMaster.command_eval d htmp).seq hsearch, ?_, ?_⟩
  · exact hout
  · intro j hj
    have heq : out.regs j = small.regs j :=
      embedState_register id localPorts before small Function.injective_id j
    rw [heq, hr j hj]
    change readRegs d.regs 0 1 none j = d.regs j
    apply StackRoutines.readRegs_frame
    all_goals intro h; have hv := congrArg Fin.val h; norm_num at hv; omega

theorem installedProgram_run (D : ℕ) (i : Fin (p^4 - 1)) (d : MasterData)
    (hquery : d.stacks 78 = thetaWord p D i)
    (hmaster : d.stacks 300 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (hclean : SubexpNodeIndexProgram.Clean (localState d)) (htmp : d.stacks 305 = []) :
    ∃ e : MasterData,
      RunsIn installedProgram
        (SubexpNodeIndexMaster.cost d +
          SubexpNodeIndexProgram.budget (thetaWord p D i)
            (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 2)
        (d.withPC (some installedProgram.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 125 (d.stacks 300))
        116 (List.replicate i.val true) ∧
      ∀ j : Fin 16, 5 ≤ j.val → e.regs j = d.regs j := by
  obtain ⟨n, hn, e, he, hs, hr⟩ := installAndSearch_eval p M D i d hquery hmaster hclean htmp
  exact ⟨e, ⟨n+1, by omega, compiled_halt_trace he 300 116⟩, hs, hr⟩

end SubexponentialSAT.SubexpNodeIndexSemantics

end OAI.Algorithms
