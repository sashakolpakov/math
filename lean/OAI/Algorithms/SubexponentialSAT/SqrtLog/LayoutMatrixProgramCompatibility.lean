import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerPreprocess

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem pairWords_eq_signedWords (ps : List Pair) : pairWords ps=BucketProgram.signedWords ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨P,N⟩
    simp [pairWords,BucketProgram.signedWords,ih]

theorem rowsWords_eq (rows : List (List Pair)) :
    rowsWords rows=Subexp.MatrixProgramSupport.words (rows.map BucketProgram.signedWords) := by
  have hf : pairWords=BucketProgram.signedWords := funext pairWords_eq_signedWords
  rw [rowsWords,hf]

theorem ids_eq_indices (js : List ℕ) : ids js=HeadScatterProgram.indices js := rfl

theorem matrixRel_dimensions {Rel : ℕ → ℕ → Pair → Prop} {B D : ℕ} {js : List ℕ}
    {rows : List (List Pair)} (h : MatrixRel Rel B D js rows) :
    rows.length=D ∧ ∀ row ∈ rows, row.length=js.length := by
  refine ⟨?_,?_⟩
  · simpa [MatrixRel] using h.length_eq.symm
  · intro row hr
    have aux : ∀ (is : List ℕ) (rs : List (List Pair)),
        List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
          is rs → ∀ row ∈ rs, row.length=js.length := by
      intro is rs hs
      induction hs with
      | nil => simp
      | cons hi ht ih =>
        intro row hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hi.length_eq.symm
        · exact ih row hr
    exact aux _ _ h row hr

def controllerRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def controllerPorts : Fin 25 → Fin 288 := Fin.castAdd 263

theorem project_finalState (base : Fin 288 → List Bool) (rf : Fin 16 → Bool)
    (W : List Bool) (js : List ℕ) (n h : ℕ) (rows : List (List Pair))
    (hbase : ∀ i : Fin 25, base (controllerPorts i)=
      (BucketProgram.Controller.signedInitial (rf ∘ controllerRegs) W [] js n h).stacks i) :
    projectState controllerRegs controllerPorts (finalState base rf rows)=
      BucketProgram.Controller.signedInitial (rf ∘ controllerRegs) W rows js n h := by
  apply congrArg (StructuredProgram.State.mk (rf ∘ controllerRegs))
  funext i
  have hbi := hbase i
  fin_cases i <;>
    simp [controllerPorts,finalState,state,rowsWords_eq,
      BucketProgram.Controller.signedInitial,BucketProgram.Controller.wideState] at hbi ⊢ <;>
    first | exact hbi

theorem ids_length_le (js : List ℕ) (n : ℕ) (h : ∀ v ∈ js, v ≤ n) :
    (ids js).length ≤ 1+(2*n+2)*js.length := by
  unfold ids
  have hh := ProgramEncoding.encodeRecords_length_le
    (js.map fun j => List.replicate j true) n (by
      intro word hw
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
      simpa using h v hv)
  simpa using hh

theorem commandCost_le_explicit (T B D n : ℕ) (js : List ℕ) (h : ∀ v ∈ js, v ≤ n) :
    commandCost T B D n js ≤
      19*(1+(2*n+2)*js.length)+12+
        D*(9*D+7*(1+(2*n+2)*js.length)+js.length*(T+24*B+8*n+45)+27) := by
  have hh := ids_length_le js n h
  unfold commandCost rowBodyCost
  calc
    _ ≤ 19*(1+(2*n+2)*js.length)+12+
        D*(9*D+7*(1+(2*n+2)*js.length)+js.length*(T+24*B+8*n+45)+25+2) := by
      gcongr
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
