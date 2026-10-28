import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInput

namespace OAI.Algorithms

/-! Whole native outer-leaf composition.  Startup is the checked actual
program, and the remaining two services carry literal native trace contracts.
Associating the fixed sequence changes neither code nor charged steps. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram

theorem nontrivial_trace (mass acceptedCount : Cmd 40 896)
    {ni nt : ℕ} {a p b : Data} (hi : Eval initialCode ni a p)
    (ht : Eval (solve mass acceptedCount) nt p b) :
    Eval (nontrivial mass acceptedCount) (ni+nt) a b := by
  change Eval (.seq start constructCode) ni a p at hi
  cases hi with
  | seq hs hc =>
    have he := hs.seq (hc.seq ht)
    simpa only [nontrivial,solve,Nat.add_assoc] using he

theorem nontrivial_from_services {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m) (hB : 0 < B)
    (mass acceptedCount : Cmd 40 896) {ni : ℕ} {a p : Data}
    (hi : Eval initialCode ni a p) (hp : StartReady p n m B)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (hrows : p.stacks 777=candidateEncoding
      (LeafScopeResourceBounds.initialPayloads (p.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q)))
    (svc : NativeServices clauses mass acceptedCount p
      (LeafScopeResourceBounds.initialPayloads (p.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q))) :
    ∃ steps b bit, Eval (nontrivial mass acceptedCount) steps a b ∧
      steps ≤ ni+svc.budget ∧ b.stacks 787=[bit] ∧
      (bit=true ↔ ∃ x, ∀ e, (clauses e).eval x=true) := by
  obtain ⟨nt,b,bit,ht,hnt,hbit,hmodels⟩ :=
    svc.run clauses hm hB mass acceptedCount p hp s Q hs hQ hrows
  exact ⟨ni+nt,b,bit,nontrivial_trace mass acceptedCount hi ht,
    Nat.add_le_add_left hnt ni,hbit,hmodels⟩

/-- The full compiled controller, including its real classifier, after an
actual startup trace.  The initial-state trace starts at the classifier's
literal returned state, so no register reset is assumed for free. -/
theorem command_from_services {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n)))
    (B : ℕ) (hB : 0 < B) (mass acceptedCount : Cmd 40 896)
    (a p : Data) (ni : ℕ)
    (hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F))
    (hready : SubexpEmptyClauseProgram.Ready
      (projectState LeafProgram.Dispatch.registers LeafProgram.Dispatch.stackMap a))
    (hnonempty : F≠[]) (hempty : [] ∉ F)
    (hi : Eval initialCode ni (classified a (formulaRecords F)) p)
    (hp : StartReady p n F.length B)
    (s : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) s)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B/(100*B*SparseCode.logSize F.length)+1))
    (hrows : p.stacks 777=candidateEncoding
      (LeafScopeResourceBounds.initialPayloads (p.stacks 768).length
        (CodeRowsProgram.serializedRows F.length s Q)))
    (svc : NativeServices (formulaClauses F) mass acceptedCount p
      (LeafScopeResourceBounds.initialPayloads (p.stacks 768).length
        (CodeRowsProgram.serializedRows F.length s Q))) :
    ∃ steps b bit, Eval (command mass acceptedCount) steps a b ∧
      steps ≤ 100*((a.stacks 784).length+1)+5+ni+svc.budget ∧
      b.stacks 787=[bit] ∧ (bit=true ↔ SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  obtain ⟨nt,b,bit,ht,hnt,hbit,hmodels⟩ := nontrivial_from_services (formulaClauses F)
    (List.length_pos_iff.mpr hnonempty) hB mass acceptedCount hi hp s Q hs hQ hrows svc
  have hr : formulaRecords F≠[] := by
    intro h
    have hl := congrArg List.length h
    rw [formulaRecords_length,List.length_nil] at hl
    exact hnonempty (List.length_eq_zero_iff.mp hl)
  obtain ⟨total,htotal,htrace⟩ := dispatch_nontrivial mass acceptedCount a
    (formulaRecords F) hformula hready
    (fun h => hempty ((formulaRecords_empty_clause F).mp h)) hr ht
  exact ⟨total,b,bit,htrace,by omega,hbit,hmodels.trans (formulaClauses_satisfiable F)⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
