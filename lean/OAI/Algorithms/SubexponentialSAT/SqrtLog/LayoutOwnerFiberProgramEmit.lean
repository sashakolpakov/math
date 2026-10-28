import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramCore
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev push := @SubexponentialSAT.Subexp.TupleProgram.pushConst 5 11
abbrev pushed := @SubexponentialSAT.Subexp.TupleProgram.pushedState 5 11

def reset (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  Function.update (status regs false true) 4 false

def normalize : Code := .seq (.base (.atom (.set 0 false)))
  (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 4 false))))

theorem normalize_eval (d : Data) : Eval normalize 3 d ⟨reset d.regs,d.stacks⟩ := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 5) false) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 5) true)
    ((StructuredProgram.Atom.set (0 : Fin 5) false).eval d))
  have h3 := Eval.base (StructuredProgram.Eval.atom (.set (4 : Fin 5) false)
    ((StructuredProgram.Atom.set (1 : Fin 5) true).eval
      ((StructuredProgram.Atom.set (0 : Fin 5) false).eval d)))
  simpa [normalize,reset,status,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h1.seq (h2.seq h3)

def emitMatch : Code := .seq (.call (StackRoutines.copyProgram 7 8 6 0 1))
  (.seq (push 8 0 false) (push 9 0 true))

theorem emitMatch_eval (regs : Fin 5 → Bool) (q m s acc out : List Bool) (j count : ℕ) :
    Eval emitMatch (7*j+9)
      (data regs q m s [] [] [] [] (unary j) acc (unary count) out)
      (data (status regs true false) q m s [] [] [] [] (unary j)
        ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out) := by
  let a := data regs q m s [] [] [] [] (unary j) acc (unary count) out
  let b := data (status regs false false) q m s [] [] [] [] (unary j)
    (unary j++acc) (unary count) out
  have h1 := copy_eval a 7 8 6 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hb : afterCopy a 7 8 0 1=b := by
    apply state_ext
    · simp [a,b,afterCopy,data]
    · funext k; fin_cases k <;> simp [a,b,afterCopy,data,StackRoutines.copyStacks]
  rw [hb] at h1
  have h2 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (8 : Fin 11) (0 : Fin 5) false b
  have h3 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (9 : Fin 11) (0 : Fin 5) true (pushed 8 0 false b)
  change Eval (push 9 0 true) 2 (pushed 8 0 false b)
    (pushed 9 0 true (pushed 8 0 false b)) at h3
  have he : pushed 9 0 true (pushed 8 0 false b)=
      data (status regs true false) q m s [] [] [] [] (unary j)
        ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out := by
    apply state_ext
    · funext k; fin_cases k <;> simp [b,status,data]
    · funext k; fin_cases k <;>
        simp [b,data,Encoding.encodeNat,
          List.reverse_append,List.replicate_succ]
  rw [he] at h3
  have hh := h1.seq (h2.seq h3)
  simpa [emitMatch,a,data,Nat.add_assoc] using hh

def finish : Code := .seq (.ite 4 emitMatch (.base .skip))
  (.seq (push 7 0 true) normalize)

theorem finish_eval (regs : Fin 5 → Bool) (q m s acc out : List Bool)
    (j count : ℕ) (matched : Bool) (hf : regs 4=matched) :
    ∃ n ≤ 7*j+15,
      Eval finish n (data regs q m s [] [] [] [] (unary j) acc (unary count) out)
        (data (reset regs) q m s [] [] [] [] (unary (j+1))
          (if matched then (Encoding.encodeNat j).reverse++acc else acc)
          (unary (count+(if matched then 1 else 0))) out) := by
  cases matched with
  | false =>
      let a := data regs q m s [] [] [] [] (unary j) acc (unary count) out
      have h1 : Eval (.ite 4 emitMatch (.base .skip)) 1 a a :=
        Eval.ite_false hf (Eval.base (StructuredProgram.Eval.skip a))
      have h2 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (7 : Fin 11) (0 : Fin 5) true a
      have h3 := normalize_eval (pushed 7 0 true a)
      refine ⟨6,by omega,?_⟩
      have he : (⟨reset (pushed 7 0 true a).regs,(pushed 7 0 true a).stacks⟩ : Data)=
          data (reset regs) q m s [] [] [] [] (unary (j+1)) acc (unary count) out := by
        apply state_ext
        · funext k; fin_cases k <;> simp [a,reset,status,data]
        · funext k; fin_cases k <;> simp [a,data,List.replicate_succ]
      rw [he] at h3
      simpa only [finish,Bool.false_eq_true,ite_false,Nat.add_zero] using h1.seq (h2.seq h3)
  | true =>
      let b := data (status regs true false) q m s [] [] [] [] (unary j)
        ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out
      have h1 := Eval.ite_true (no := (.base .skip)) hf (emitMatch_eval regs q m s acc out j count)
      have h2 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (7 : Fin 11) (0 : Fin 5) true b
      have h3 := normalize_eval (pushed 7 0 true b)
      refine ⟨7*j+15,le_rfl,?_⟩
      have he : (⟨reset (pushed 7 0 true b).regs,(pushed 7 0 true b).stacks⟩ : Data)=
          data (reset regs) q m s [] [] [] [] (unary (j+1))
            ((Encoding.encodeNat j).reverse++acc) (unary (count+1)) out := by
        apply state_ext
        · funext k; fin_cases k <;> simp [b,reset,status,data]
        · funext k; fin_cases k <;> simp [b,data,List.replicate_succ]
      rw [he] at h3
      have hh := h1.seq (h2.seq h3)
      simpa [finish,b,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
