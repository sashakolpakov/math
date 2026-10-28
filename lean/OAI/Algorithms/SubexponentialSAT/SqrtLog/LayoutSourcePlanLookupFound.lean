import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupFoundCore

namespace OAI.Algorithms

/-! The same frozen pair-lookup program exposes its native found bit in register4.
No extra scan, metadata value, or runtime instruction is introduced. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Scan
theorem command_eval_found (regs : Fin 16 → Bool) (literal ambient factor query : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ SubexpNodeIndexProgram.Internal.budget query nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] query [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] []) ∧
      rf 4=decide (query ∈ nodes) := by
  let d := data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
    [] [] query [] [] [] [] []
  let rr := fun i => regs (register i)
  obtain ⟨n,hn,rs,he,hflag⟩ := SubexpNodeIndexProgram.Internal.command_eval_found rr query nodes
  have ha : projectState register stack d =
      SubexpNodeIndexProgram.Internal.state rr query
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [←ha] at he
  have hh := eval_liftCommand_from_state SubexpNodeIndexProgram.Internal.command 0 6
    register stack d register_injective stack_injective he
  let e := embedState register stack d
    (SubexpNodeIndexProgram.Internal.state rs query (ProgramEncoding.encodeRecords nodes)
      [] [] [] [] (List.replicate (nodes.idxOf query) true))
  have hb : e = data e.regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
      (List.replicate (nodes.idxOf query) true) [] query [] [] [] [] [] := by
    apply embedState_eq register stack register_injective stack_injective
    · intro i
      exact embedState_register register stack d _ register_injective i
    · intro i; fin_cases i <;> rfl
    · intro i hi
      exact embedState_register_frame register stack d _ i hi
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact False.elim (hi ⟨0,rfl⟩)
        | exact False.elim (hi ⟨1,rfl⟩)
        | exact False.elim (hi ⟨2,rfl⟩)
        | exact False.elim (hi ⟨3,rfl⟩)
        | exact False.elim (hi ⟨4,rfl⟩)
        | exact False.elim (hi ⟨5,rfl⟩)
        | exact False.elim (hi ⟨6,rfl⟩)
  refine ⟨n+1,hn,e.regs,?_,?_⟩
  · change Eval command (n+1) d e at hh
    rw [hb] at hh
    exact hh
  · have hg : e.regs (register 4)=rs 4 :=
      embedState_register register stack d _ register_injective 4
    exact hg.trans hflag

end Scan

namespace Local
theorem command_eval_found (regs : Fin 16 → Bool) (literal ambient factor : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ budget literal ambient factor nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] [] [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf (pairKey literal (ambient++factor))) true)
          [] [] [] [] [] [] []) ∧
      rf 4=decide (pairKey literal (ambient++factor) ∈ nodes) := by
  obtain ⟨r1,h1⟩ := buildQuery_eval regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
  obtain ⟨n,hn,r2,h2,hflag⟩ := Scan.command_eval_found r1 literal ambient factor
    (pairKey literal (ambient++factor)) nodes
  let q := pairKey literal (ambient++factor)
  let count := List.replicate (nodes.idxOf q) true
  let d := data r2 literal ambient factor (ProgramEncoding.encodeRecords nodes)
    count [] q [] [] [] [] []
  have h3 := clear_eval 6 d
  have he : (⟨readRegs d.regs 0 1 none,Function.update d.stacks 6 []⟩ : Data)=
      data (readRegs r2 0 1 none) literal ambient factor (ProgramEncoding.encodeRecords nodes)
        count [] [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [d,data]
  rw [he] at h3
  refine ⟨31*(literal.length+ambient.length+factor.length)+88+
    (n+(2*q.length+3)),?_,readRegs r2 0 1 none,?_,?_⟩
  · simp only [budget,q,pairKey_length,List.length_append] at *
    omega
  · exact h1.seq (h2.seq h3)

  · simpa [readRegs] using hflag

end Local

namespace Native
theorem command_eval_found (d : Data) (nodes : List (List Bool))
    (hmaster : d.stacks 337=ProgramEncoding.encodeRecords nodes) (hclean : Clean d) :
    ∃ n ≤ budget d nodes, ∃ e : Data,
      Eval command n d e ∧
      e.stacks=Function.update d.stacks 304
        (List.replicate (nodes.idxOf
          (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true) ∧
      e.regs 4=decide (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216) ∈ nodes) := by
  have h304 := hclean 304 (by simp)
  have h315 := hclean 315 (by simp)
  have h316 := hclean 316 (by simp)
  have h317 := hclean 317 (by simp)
  have h318 := hclean 318 (by simp)
  have h319 := hclean 319 (by simp)
  have h338 := hclean 338 (by simp)
  have h339 := hclean 339 (by simp)
  obtain ⟨n,hn,rs,he,hflag⟩ := Local.command_eval_found d.regs
    (d.stacks 233) (d.stacks 212) (d.stacks 216) nodes
  have ha : projectState id stack d =
      data d.regs (d.stacks 233) (d.stacks 212) (d.stacks 216)
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;>
        simp [projectState,stack,data,hmaster,h304,h315,h316,h317,h318,h319,h338,h339]
  rw [←ha] at he
  have hh := eval_liftCommand_from_state Local.command 0 4 id stack d
    Function.injective_id stack_injective he
  let count := List.replicate (nodes.idxOf
    (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true
  let e := embedState id stack d
    (data rs (d.stacks 233) (d.stacks 212) (d.stacks 216)
      (ProgramEncoding.encodeRecords nodes) count [] [] [] [] [] [] [])
  refine ⟨n+1,Nat.add_le_add_right hn 1,e,hh,?_,?_⟩
  · funext j
    by_cases hj : ∃ i, stack i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [show e.stacks (stack i)=_ from embedState_stack id stack d _ stack_injective i]
      fin_cases i <;>
        simp [stack,data,count,hmaster,h315,h316,h317,h318,h319,h338,h339]
    · have hj304 : j≠304 := fun h => hj ⟨4,by simpa [stack] using h.symm⟩
      rw [Function.update_of_ne hj304]
      exact embedState_stack_frame id stack d _ j hj
  · have hg : e.regs ((id : Fin 16 → Fin 16) 4)=rs 4 :=
      embedState_register id stack d _ Function.injective_id 4
    exact hg.trans hflag

end Native

theorem pairKey_mem_records (ps : List (ℕ × ℕ)) (v f : ℕ) :
    pairKey (unary v) (unary f) ∈ records ps ↔ (v,f) ∈ ps := by
  change payload (v,f) ∈ ps.map payload ↔ (v,f) ∈ ps
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    have hpeq := payload_injective he
    simpa only [hpeq] using hp
  · intro h
    exact List.mem_map.mpr ⟨(v,f),h,rfl⟩

/-- Register4 is the actual full-pair membership result, including the miss case.
This strengthens the frozen native command without adding an instruction. -/
theorem pair_command_eval_found (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f)
    (hmaster : d.stacks 337=LayoutOwnerFiberProgram.stream ps) (hc : Native.Clean d) :
    ∃ k, k+1 ≤ pairBudget v n f ps ∧ ∃ e : Native.Data,
      Eval Native.command k d e ∧
      e.stacks=Function.update d.stacks 304 (unary (ps.idxOf (v,n+f))) ∧
      e.regs 4=decide ((v,n+f) ∈ ps) := by
  have hm : d.stacks 337=ProgramEncoding.encodeRecords (records ps) := by
    simpa only [records_stream] using hmaster
  obtain ⟨k,hk,e,he,hs,hflag⟩ := Native.command_eval_found d (records ps) hm hc
  have hu : unary n++unary f=unary (n+f) := (List.replicate_add n f true).symm
  rw [hv,hn,hf,hu,records_idxOf] at hs
  simp only [hv,hn,hf,hu,pairKey_mem_records] at hflag
  refine ⟨k,?_,e,he,hs,hflag⟩
  rw [←pair_budget_eq d ps v n f hv hn hf]
  omega

theorem pair_program_run_found (d : Native.Data) (ps : List (ℕ × ℕ)) (v n f : ℕ)
    (hv : d.stacks 233=unary v) (hn : d.stacks 212=unary n)
    (hf : d.stacks 216=unary f)
    (hmaster : d.stacks 337=LayoutOwnerFiberProgram.stream ps) (hc : Native.Clean d) :
    ∃ e : Native.Data,
      RunsIn Native.program (pairBudget v n f ps)
        (d.withPC (some Native.program.entry)) (e.withPC none) ∧
      e.stacks=Function.update d.stacks 304 (unary (ps.idxOf (v,n+f))) ∧
      e.regs 4=decide ((v,n+f) ∈ ps) := by
  obtain ⟨k,hk,e,he,hs,hflag⟩ := pair_command_eval_found d ps v n f hv hn hf hmaster hc
  exact ⟨e,⟨k+1,hk,compiled_halt_trace he 233 304⟩,hs,hflag⟩

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
