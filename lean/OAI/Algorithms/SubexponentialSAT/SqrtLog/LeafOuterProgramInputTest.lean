import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInput
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyObserved

namespace OAI.Algorithms

/-! A proof-only Boolean name for the semantics of encoded leaves.  The native
machine never executes this definition; its actual trace proves the value. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT

def inputBits {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) : List Bool :=
  Encoding.encodeList id (formulaRecords F)

theorem inputBits_injective (n : ℕ) :
    Function.Injective (inputBits (n:=n)) := by
  intro F G h
  have hr : formulaRecords F=formulaRecords G :=
    Encoding.encodeList_injective Function.injective_id h
  exact (List.map_injective_iff.mpr
    (Encoding.encodeList_injective ExecSunflowerCodeTransport.literalWord_injective)) hr

theorem inputBits_eq_observed {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) :
    inputBits F=ExecSparsifyObserved.encode F := by
  simp only [inputBits,formulaRecords,ExecSparsifyObserved.encode,
    CandidatePrepareProgram.formulaCode,CandidatePrepareProgram.clauseCode,
    ExecSparsifyEncoding.words,ExecSparsifyEncoding.encodeList_map,id_eq]

noncomputable def inputTest (n : ℕ) (bits : List Bool) : Bool := by
  classical
  exact decide (∃ F : ExecCNF.Formula (SAT.Literal (Fin n)),
    inputBits F=bits ∧ SAT.Satisfiable (ExecCNF.formulaSet F))

theorem inputTest_spec {n : ℕ} (F : ExecCNF.Formula (SAT.Literal (Fin n))) :
    inputTest n (inputBits F)=true ↔ SAT.Satisfiable (ExecCNF.formulaSet F) := by
  classical
  simp only [inputTest,decide_eq_true_eq]
  constructor
  · rintro ⟨G,hG,hSAT⟩
    exact (inputBits_injective n hG) ▸ hSAT
  · intro hSAT
    exact ⟨F,rfl,hSAT⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
