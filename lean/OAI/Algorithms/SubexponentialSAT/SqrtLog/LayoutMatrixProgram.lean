import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramInitialize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramLoop

namespace OAI.Algorithms

/-! Direct all-incidence-row signed matrix construction by one fixed program.
The entry dependency is an explicit native finite-bank command contract. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

@[simp] theorem ids_reverse_length (js : List ℕ) : (ids js.reverse).length=(ids js).length := by
  simp [ids,List.map_reverse,ProgramEncoding.encodeRecords_length]

def clearIDs : Code 288 := .call (StackRoutines.clearProgram 282 0 1)

theorem clearIDs_eval (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    Eval clearIDs (2*q.reversedIDs.length+3) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with reversedIDs:=[]}) := by
  have h := Subexp.TupleProgram.clear_eval (282 : Fin 288) (0 : Fin 16) 1 (state base regs q)
  convert h using 1 <;> first
    | rfl
    | exact congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
        (update_reversedIDs base regs q []).symm

def command (entry : Code 256) : Code 288 :=
  .seq initializeIDs (.seq (rowLoop entry) clearIDs)

def initialState (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (D : ℕ) : Data 288 :=
  state base regs {remaining:=List.replicate D true}

def finalState (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (rows : List (List Pair)) : Data 288 := state base regs {matrix:=rowsWords rows}

def commandCost (T B D n : ℕ) (js : List ℕ) : ℕ :=
  19*(ids js).length+12+D*(rowBodyCost T B n D (ids js).length js.length+2)

def MatrixRel (Rel : ℕ → ℕ → Pair → Prop) (B D : ℕ) (js : List ℕ)
    (rows : List (List Pair)) : Prop :=
  List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
    (List.range D) rows

theorem command_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v)
    (hbound : ∀ v ∈ js, v ≤ n) (regs : Fin 16 → Bool) :
    ∃ t ≤ commandCost T B D n js, ∃ rf rows,
      Eval (command entry) t (initialState base regs D) (finalState base rf rows) ∧
      MatrixRel Rel B D js rows := by
  let q₀ : Store := {remaining:=List.replicate D true}
  obtain ⟨ti,hti,ri,hei⟩ := initializeIDs_eval base hb hb' regs q₀ js hi rfl rfl
  let q₁ : Store := {q₀ with todo:=[],reversedIDs:=ids js.reverse}
  obtain ⟨tl,htl,rl,rows,hel,hrel⟩ := rowLoop_eval entry base hb hb' Valid Rel T B hc D n js
    hvalid hbound ri q₁ rfl rfl rfl rfl rfl rfl rfl rfl
  let q₂ : Store := {q₁ with remaining:=[],matrix:=rowsWords rows++q₁.matrix}
  have hec := clearIDs_eval base rl q₂
  refine ⟨ti+(tl+(2*(ids js.reverse).length+3)),?_,readRegs rl 0 1 none,rows,?_,hrel⟩
  · simp only [ids_reverse_length] at *
    unfold commandCost
    omega
  · simpa [command,initialState,finalState,q₀,q₁,q₂] using hei.seq (hel.seq hec)

/-- The compiler produces one finite instruction table, independent of all
runtime dimensions and entry magnitudes. -/
def program (entry : Code 256) := compiled (command entry) 281 24

theorem program_runsIn (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v)
    (hbound : ∀ v ∈ js, v ≤ n) (regs : Fin 16 → Bool) :
    ∃ rf rows,
      RunsIn (program entry) (commandCost T B D n js+1)
        ((initialState base regs D).withPC (some (program entry).entry))
        ((finalState base rf rows).withPC none) ∧ MatrixRel Rel B D js rows := by
  obtain ⟨t,ht,rf,rows,he,hr⟩ := command_eval entry base hb hb' Valid Rel T B hc D n js
    hi hvalid hbound regs
  exact ⟨rf,rows,⟨t+1,by omega,compiled_halt_trace he 281 24⟩,hr⟩

theorem program_primitive_runsIn (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v)
    (hbound : ∀ v ∈ js, v ≤ n) (regs : Fin 16 → Bool) :
    ∃ rf rows,
      Computation.RunsIn (primitive (program entry)).step
        (primitiveOverhead (program entry)*(commandCost T B D n js+1))
        (primitiveCfg (program entry) ((initialState base regs D).withPC (some (program entry).entry)))
        (primitiveCfg (program entry) ((finalState base rf rows).withPC none)) ∧
      MatrixRel Rel B D js rows := by
  obtain ⟨rf,rows,⟨t,ht,he⟩,hr⟩ := program_runsIn entry base hb hb' Valid Rel T B hc D n js
    hi hvalid hbound regs
  obtain ⟨u,hu,he'⟩ := primitive_trace (program entry) he
  exact ⟨rf,rows,⟨u,hu.trans (Nat.mul_le_mul_left _ ht),he'⟩,hr⟩

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
