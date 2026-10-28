import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramLookupBound

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The finite tape layout of additive sparse insertion. All fields are runtime
bit strings; this record is used only to state the physical program invariant. -/
structure Tape where
  modulus : List Bool := []
  width : List Bool := []
  count : List Bool := []
  dict : List Bool := []
  query : List Bool := []
  coeff : List Bool := []
  remain : List Bool := []
  found : List Bool := []
  left : List Bool := []
  right : List Bool := []
  out : List Bool := []
  steps : List Bool := []
  result : List Bool := []
  combined : List Bool := []

def tapes (a : Tape) : Fin 27 → List Bool := fun i =>
  if i = 0 then a.out else if i = 5 then a.modulus else
  if i = 8 then a.left else if i = 9 then a.right else
  if i = 11 then a.steps else if i = 12 then a.width else
  if i = 15 then a.dict else if i = 16 then a.query else
  if i = 17 then a.coeff else if i = 18 then a.remain else
  if i = 22 then a.found else if i = 24 then a.count else
  if i = 25 then a.result else if i = 26 then a.combined else []

def machine (regs : Fin 8 → Bool) (a : Tape) : Data := ⟨regs,tapes a⟩

noncomputable def overlay (regs : Fin 8 → Bool) (rr : Fin 5 → Bool) : Fin 8 → Bool :=
  Function.extend smallRegs rr regs

theorem overlay_same (regs : Fin 8 → Bool) : overlay regs (regs ∘ smallRegs) = regs := by
  funext i
  by_cases h : ∃ j, smallRegs j = i
  · obtain ⟨j,rfl⟩ := h
    exact smallRegs_injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ h

theorem embed_lookup (regs : Fin 8 → Bool) (a : Tape)
    (rr : Fin 5 → Bool) (remain found : List Bool) :
    embedState smallRegs lookupStacks (machine regs a)
      (SubexponentialSAT.SubexpRecordScan.recordState rr remain [] a.query [] [] found) =
    machine (overlay regs rr) { a with remain := remain, found := found } := by
  apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective lookupStacks_injective
  · intro i; exact smallRegs_injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,lookupStacks,Fin.exists_fin_succ]

theorem lookup_eval (regs : Fin 8 → Bool) (a : Tape)
    (query : List Bool) (entries : List (List Bool × List Bool))
    (hq : a.query = query.reverse) (hr : a.remain = Squarefree.Program.lookupRecords entries)
    (hf : a.found = []) :
    ∃ n ≤ Squarefree.Program.lookupBudget query entries + 3, ∃ rr remain,
      Eval lookup n (machine regs a)
        (machine (overlay regs rr) { a with remain := remain, found := Squarefree.Program.lookupResult (entries.lookup query) }) ∧
      rr 4 = (entries.lookup query).isSome ∧
      remain.length ≤ (Squarefree.Program.lookupRecords entries).length := by
  obtain ⟨n,hn,rr,remain,he,hflag,hrest⟩ :=
    Squarefree.Program.dictionaryLookup_eval_tail query entries (regs ∘ smallRegs)
  have ht := compiled_halt_trace he 0 5
  have hh := eval_call_lifted Squarefree.Program.dictionaryLookupProgram smallRegs lookupStacks
    (machine regs a) smallRegs_injective lookupStacks_injective ht
  have ha : embedState smallRegs lookupStacks (machine regs a)
      (SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ smallRegs)
        (Squarefree.Program.lookupRecords entries) [] query.reverse [] [] []) = machine regs a := by
    rw [←hq,embed_lookup,overlay_same]
    congr 1
    cases a
    simp_all
  rw [ha,←hq,embed_lookup] at hh
  exact ⟨n+1,by omega,rr,remain,hh,hflag,hrest⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
