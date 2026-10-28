import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram
open IdempotentApplyProgram.Bounds

theorem recordState_eq {n B d : ℕ} (base : Fin 768 → List Bool)
    (regs : Fin 40 → Bool) (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool) :
    recordState base regs seed v pr f source payload =
      state base (recordState base regs seed v pr f source payload).regs seed source payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases h149 : i=149 <;> by_cases h150 : i=150 <;>
      simp [Factor.ports,state,Function.update_apply,h149,h150]

theorem recordState_self {n B d : ℕ} (base : Fin 768 → List Bool)
    (regs : Fin 40 → Bool) (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool)
    (h13 : regs 13=v) (h14 : regs 14=pr) (h15 : regs 15=f) :
    recordState base regs seed v pr f source payload = state base regs seed source payload := by
  rw [recordState_eq]
  congr 1
  funext i
  by_cases h1 : i=13 <;> by_cases h2 : i=14 <;> by_cases h3 : i=15 <;>
    simp_all [recordState,RecordPrograms.state,Factor.ports,state]

theorem inner_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract u J step ready eligible T C)
    (base : Fin 768 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : Good Finset.univ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids seed out ∧
      ∃ k ≤ 1+RecordPrograms.budget (fun _ => C) (records ids), ∃ rr,
        Eval (RecordPrograms.loop Factor.ports Factor.callback) k
          (RecordPrograms.afterTag Factor.ports (state base regs seed [] []) (records ids) [])
          (recordState base rr out false true false [] []) := by
  induction ids generalizing seed regs with
  | nil =>
    refine ⟨seed,hg,.nil seed,1,by simp [records,RecordPrograms.budget],regs,?_⟩
    apply Eval.while_false
    simp [RecordPrograms.afterTag,records,Factor.ports,RecordPrograms.state]
  | cons fid ids ih =>
    let bits := Encoding.encodeNat fid
    let tail := Encoding.encodeList id (records ids) ++ []
    let parsed := recordState base regs seed false true false tail bits.reverse
    obtain ⟨next,hnext,hstep,k,hk,rr,hcall,h13,h14,h15⟩ :=
      contract base hb fid seed tail parsed.regs (hids fid (by simp)) hg (by
        have hh : (ProgramEncoding.encodeRecords (records ids)).length ≤ T := by
          simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
            List.length_cons,List.length_append] at hlen ⊢
          omega
        simpa [tail,ProgramEncoding.encodeRecords] using hh)
    have hcall' : Eval Factor.callback k parsed
        (recordState base rr next false true false tail []) := by
      rw [recordState_self base rr next false true false tail [] h13 h14 h15]
      have hp : parsed = state base parsed.regs seed tail bits.reverse :=
        recordState_eq base regs seed false true false tail bits.reverse
      rw [hp]
      exact hcall
    have hreader : Eval (RecordPrograms.reader Factor.ports) (6*bits.length+4)
        (RecordPrograms.afterTag Factor.ports (state base regs seed [] []) (records (fid::ids)) [])
        parsed := by
      simpa [parsed,recordState,records,RecordPrograms.afterTag,bits,tail] using
        RecordPrograms.reader_eval Factor.ports (state base regs seed [] []) bits tail [] true true false
    have hbranch : Eval
        (.ite Factor.ports.found (RecordPrograms.atom (.set Factor.ports.tag false))
          (RecordPrograms.atom (.pop Factor.ports.source Factor.ports.tag Factor.ports.present))) 2
        (recordState base rr next false true false tail [])
        (RecordPrograms.afterTag Factor.ports (state base rr next [] []) (records ids) []) := by
      apply Eval.ite_false (by simp [recordState])
      exact RecordPrograms.pop_list_eval Factor.ports (state base rr next [] []) (records ids) [] false true
    obtain ⟨out,hout,hrel,m,hm,rf,hrest⟩ := ih next rr hnext (fun id hi => hids id (by simp [hi])) (by
      simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
        List.length_cons,List.length_append] at hlen ⊢
      omega)
    have hguard :
        (RecordPrograms.afterTag Factor.ports (state base regs seed [] []) (records (fid::ids)) []).regs
          Factor.ports.tag=true := by simp [RecordPrograms.afterTag,records]
    refine ⟨out,hout,.cons hstep hrel,(6*bits.length+4+(k+2))+m+1,?_,rf,?_⟩
    · simp only [records,List.map_cons,RecordPrograms.budget] at hm ⊢
      dsimp [bits]
      omega
    · exact Eval.while_true hguard (hreader.seq (hcall'.seq hbranch)) hrest

theorem loop_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract u J step ready eligible T C)
    (base : Fin 768 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : Good Finset.univ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids seed out ∧
      ∃ k ≤ loopBudget C ids, ∃ rr,
        Eval Factor.loop k
          (state base regs seed (ProgramEncoding.encodeRecords (records ids)) [])
          (state base rr out [] []) := by
  obtain ⟨out,hout,hr,k,hk,rr,he⟩ := inner_eval u J step ready eligible T C contract base hb ids seed regs hg hids hlen
  let initial := state base regs seed (ProgramEncoding.encodeRecords (records ids)) []
  have hstart : recordState base regs seed (regs 13) (regs 14) (regs 15)
      (Encoding.encodeList id (records ids) ++ []) [] = initial := by
    rw [recordState_self base regs seed _ _ _ _ _ rfl rfl rfl]
    simp [initial,ProgramEncoding.encodeRecords]
  have hset := RecordPrograms.set_found_eval Factor.ports (state base regs seed [] [])
    (regs 13) (regs 14) (regs 15) false (Encoding.encodeList id (records ids) ++ []) []
  have hpop := RecordPrograms.pop_list_eval Factor.ports (state base regs seed [] [])
    (records ids) [] (regs 13) (regs 14)
  have hrun := hset.seq (hpop.seq he)
  change Eval Factor.loop (1+(1+k))
    (recordState base regs seed (regs 13) (regs 14) (regs 15) _ [])
    (recordState base rr out false true false [] []) at hrun
  rw [hstart,recordState_eq] at hrun
  exact ⟨out,hout,hr,1+(1+k),by dsimp [loopBudget]; omega,_,hrun⟩

theorem loopBudget_le (C : ℕ) (ids : List ℕ) :
    loopBudget C ids ≤ (C+17)*((ProgramEncoding.encodeRecords (records ids)).length+1) := by
  have h := RecordPrograms.program_budget_le_input (fun _ => C) (records ids) 0 C (by simp)
  simp only [Nat.zero_add] at h
  dsimp [loopBudget]
  omega
end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
