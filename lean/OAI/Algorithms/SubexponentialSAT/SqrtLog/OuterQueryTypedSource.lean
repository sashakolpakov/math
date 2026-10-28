import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryProvenance

namespace OAI.Algorithms

/-! Transport the actual ordered formula to the frontend's equal ambient
index type. Transport changes neither literal bytes nor Boolean semantics. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery
open SubexponentialSAT BitProgram StructuredCalls
open LeafOuterProgram

def transportFormula {n N : ℕ} (F : Formula n) (h : n=N) : Formula N := h ▸ F

theorem transportFormula_bytes {n N : ℕ} (F : Formula n) (h : n=N) :
    HashInputProgram.Expansion.encodedClauses (transportFormula F h)=
      HashInputProgram.Expansion.encodedClauses F := by
  subst N
  rfl

theorem transportFormula_eval {n N : ℕ} (F : Formula n) (h : n=N) (x : Fin N → Bool) :
    SAT.CNF.eval x (ExecCNF.formulaSet (transportFormula F h))=
      SAT.CNF.eval (fun v => x (Fin.cast h v)) (ExecCNF.formulaSet F) := by
  subst N
  rfl

theorem transportFormula_satisfiable {n N : ℕ} (F : Formula n) (h : n=N) :
    SAT.Satisfiable (ExecCNF.formulaSet (transportFormula F h)) ↔
      SAT.Satisfiable (ExecCNF.formulaSet F) := by
  subst N
  rfl

def querySource {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) (N : ℕ)
    (hN : N=ProducedQueryResources.ambient (query F a rows mark)) : Formula N :=
  transportFormula F ((query_ambient F a ha rows mark).symm.trans hN.symm)

theorem querySource_bytes {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) (N : ℕ)
    (hN : N=ProducedQueryResources.ambient (query F a rows mark)) :
    (query F a rows mark).clauses=
      HashInputProgram.Expansion.encodedClauses (querySource F a ha rows mark N hN) :=
  (query_source F a rows mark).trans (transportFormula_bytes F _).symm

theorem querySource_satisfiable {n B : ℕ} (F : Formula n) (a : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) (N : ℕ)
    (hN : N=ProducedQueryResources.ambient (query F a rows mark)) :
    SAT.Satisfiable (ExecCNF.formulaSet (querySource F a ha rows mark N hN)) ↔
      SAT.Satisfiable (ExecCNF.formulaSet F) := transportFormula_satisfiable F _

theorem sourceClause_set {n : ℕ} (F : Formula n) (i : Fin (formulaRecords F).length) :
    ExecCNF.clauseSet (sourceClause F i)=
      formulaClauses F (Fin.cast (formulaRecords_length F) i) := rfl

theorem query_clause_count {n : ℕ} (F : Formula n) (a : Data)
    (rows : HashScopeProgram.RawTable.Rows (formulaRecords F).length)
    (mark : Option (Fin (formulaRecords F).length)) :
    (query F a rows mark).clauses.length=F.length := formulaRecords_length F

end SubexponentialSAT.SqrtLog.OuterQuery

end OAI.Algorithms
