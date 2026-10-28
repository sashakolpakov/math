import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem embed_replacement (regs : Fin 8 → Bool) (rr : Fin 5 → Bool)
    (a : Tape) (dict query result combined : List Bool) (hr : a.remain = []) :
    embedState smallRegs replaceStacks (machine regs a)
      (Squarefree.Program.keepCoefficient
        (Squarefree.Program.eraseData rr dict query result []) combined) =
    machine (overlay regs rr) { a with dict := dict, query := query.reverse, result := result, combined := combined } := by
  apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective replaceStacks_injective
  · intro i; exact smallRegs_injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> simp [machine,tapes,replaceStacks,
      Squarefree.Program.keepCoefficient,Squarefree.Program.eraseData,Squarefree.Program.extendStorage,SubexponentialSAT.SubexpRecordScan.storage,hr]
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,replaceStacks,Fin.exists_fin_succ]

theorem replace_eval (regs : Fin 8 → Bool) (a : Tape)
    (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (hd : a.dict = Squarefree.Program.rawEntries entries)
    (hq : a.query = query.reverse) (hc : a.combined = coeff.reverse)
    (hr : a.remain = []) (hout : a.result = []) :
    ∃ n ≤ Squarefree.Program.eraseBudget query entries + 4 * query.length + 4 * coeff.length + 17,
    ∃ rr, Eval replace n (machine regs a)
      (machine (overlay regs rr) { a with dict := [], query := [], result := Squarefree.Program.rawEntries ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse), combined := [] }) := by
  obtain ⟨n,hn,rr,ht⟩ := Squarefree.Program.dictionaryReplace_trace entries query coeff (regs ∘ smallRegs)
  have hh := eval_call_lifted Squarefree.Program.dictionaryReplaceProgram smallRegs replaceStacks
    (machine regs a) smallRegs_injective replaceStacks_injective ht
  simp only [Squarefree.Program.replaceData,Squarefree.Program.replaceDone] at hh
  rw [embed_replacement _ _ _ _ _ _ _ hr,embed_replacement _ _ _ _ _ _ _ hr,overlay_same] at hh
  have ha : { a with dict := Squarefree.Program.rawEntries entries, query := query.reverse, result := [], combined := coeff.reverse } = a := by cases a; simp_all
  rw [ha] at hh
  exact ⟨n,hn,rr,hh⟩

theorem rawEntries_eq_lookupRecords (entries : List (List Bool × List Bool)) :
    Squarefree.Program.rawEntries entries = Squarefree.Program.lookupRecords entries := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    simp only [Squarefree.Program.rawEntries,List.flatMap_cons,Squarefree.Program.lookupRecords,
      SubexponentialSAT.Subexp.SelectorProgram.rawRecords] at *
    simpa only [List.append_assoc] using congrArg (fun t => Encoding.frame a.1 ++ Encoding.frame a.2 ++ t) ih

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
