import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoop

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def rawInput {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) : List Bool :=
  (terms.map (word b m)).flatten.reverse

theorem scanInput_append {m : ℕ} (b : ℕ) (xs ys : List (Fin m × ZMod 3)) :
    scanInput b (xs++ys)=scanInput b xs++scanInput b ys := by
  simp [scanInput,List.flatten_append]

theorem scanInput_reverse {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) :
    scanInput b terms.reverse=rawInput b terms := by
  induction terms with
  | nil => rfl
  | cons a terms ih =>
      rw [List.reverse_cons,scanInput_append,ih]
      have ha : scanInput b [a]=(word b m a).reverse := by simp [scanInput]
      rw [ha]
      simp [rawInput]

theorem original_payload_length_le (clauses : List (List Bool)) (p : List Bool)
    (hp : p∈clauses) : p.length ≤ (Encoding.encodeList id clauses).length := by
  induction clauses with
  | nil => simp at hp
  | cons q qs ih =>
      have hq := Encoding.length_frame q
      simp only [Encoding.encodeList,id_eq,Encoding.length_frame,List.length_cons,List.length_append] at *
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have hh := ih hp
        omega

def uniformBudget (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (count : ℕ) : ℕ :=
  3+count*(termBudget b modulus.length clauses.length (Encoding.encodeList id clauses).length
    ((d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) (Encoding.encodeList id clauses).length+4)

theorem loopBudget_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (terms : List (Fin clauses.length × ZMod 3)) :
    loopBudget t d b modulus.length clauses terms ≤ uniformBudget t d b modulus clauses terms.length := by
  induction terms with
  | nil => simp [loopBudget,uniformBudget]
  | cons a terms ih =>
      have hc := original_payload_length_le clauses clauses[a.1.val] (List.getElem_mem a.1.isLt)
      simp only [loopBudget,uniformBudget,List.map_cons,List.sum_cons,List.length_cons] at *
      unfold termBudget at *
      nlinarith

abbrev initializeRow : Cmd 8 24 := .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 16 0)))

theorem initializeRow_eval (regs : Fin 8 → Bool) (raw width modulus master shape : List Bool) :
    Eval initializeRow 2 (data regs raw width modulus master shape [] [] [] [] [])
      (data (Function.update regs 0 false) raw width modulus master shape [false] [] [] [] []) := by
  let a := data regs raw width modulus master shape [] [] [] [] []
  let b := (StructuredProgram.Atom.set (0 : Fin 8) false).eval a
  have h1 : Eval (.base (.atom (.set 0 false))) 1 a b := .base (.atom _ _)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (16 : Fin 24) 0) b)
  convert h1.seq h2 using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [a,b,data,tapes,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

abbrev assemble : Cmd 8 24 := .seq initializeRow loop
def assembleProgram := compiled assemble 0 16

/-- The input is only the reversed raw tuple plus the original source bytes
and dynamic size data. The fully inlined payload is produced by the run. -/
theorem assemble_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ uniformBudget t d b modulus clauses terms.length+2, ∃ rf,
      Eval assemble n
        (data regs (rawInput b terms) width modulus (Encoding.encodeList id clauses)
          shape [] [] [] [] [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (Encoding.encodeList id (terms.map (payload t d clauses))) [] [] [] []) := by
  have hi := initializeRow_eval regs (rawInput b terms) width modulus (Encoding.encodeList id clauses) shape
  obtain ⟨n,hn,rf,he⟩ := loop_eval t d ht b hb clauses terms.reverse hbound
    (Function.update regs 0 false) width modulus shape [false] hw hm hshape
  rw [scanInput_reverse,List.reverse_reverse] at he
  have hh (ps : List (List Bool)) : records ps [false]=Encoding.encodeList id ps := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
        change true::(Encoding.frame p++records ps [false]) =
          true::(Encoding.frame p++Encoding.encodeList id ps)
        rw [ih]
  rw [hh] at he
  have hcost := loopBudget_le t d b modulus clauses terms.reverse
  simp only [List.length_reverse] at hcost
  exact ⟨2+n,by omega,rf,hi.seq he⟩

theorem assemble_runs (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn assembleProgram (uniformBudget t d b modulus clauses terms.length+3)
      ((data regs (rawInput b terms) width modulus (Encoding.encodeList id clauses)
        shape [] [] [] [] []).withPC (some assembleProgram.entry))
      ((data rf [] width modulus (Encoding.encodeList id clauses) shape
        (Encoding.encodeList id (terms.map (payload t d clauses))) [] [] [] []).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := assemble_eval t d ht b hb clauses terms hbound regs width modulus shape hw hm hshape
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 16⟩

theorem assemble_primitive (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, Computation.RunsIn (primitive assembleProgram).step
      (primitiveOverhead assembleProgram*(uniformBudget t d b modulus clauses terms.length+3))
      (primitiveCfg assembleProgram
        ((data regs (rawInput b terms) width modulus (Encoding.encodeList id clauses)
          shape [] [] [] [] []).withPC (some assembleProgram.entry)))
      (primitiveCfg assembleProgram
        ((data rf [] width modulus (Encoding.encodeList id clauses) shape
          (Encoding.encodeList id (terms.map (payload t d clauses))) [] [] [] []).withPC none)) := by
  obtain ⟨rf,hr⟩ := assemble_runs t d ht b hb clauses terms hbound regs width modulus shape hw hm hshape
  exact ⟨rf,SubexponentialSAT.BitProgram.primitive_execution assembleProgram hr⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
