import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramNativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedFrame

namespace OAI.Algorithms

/-! The marked branch appends one scope even when that scope is empty. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


abbrev clearEll : Cmd 11 80 := .call (StackRoutines.clearProgram 72 8 9)
abbrev moveScope : Cmd 11 80 := .call (StackRoutines.transferProgram 73 47 8 9)

theorem clearEll_eval (rf : Fin 11 → Bool) (width modulus master shape out clause : List Bool) :
    Eval clearEll 5 (data rf width modulus master shape out [] [] clause [true] [])
      (data (readRegs rf 8 9 none) width modulus master shape out [] [] clause [] []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (72 : Fin 80) (8 : Fin 11) 9
    (data rf width modulus master shape out [] [] clause [true] [])
  convert h using 1
  · simp [data, tapes]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> simp [data,tapes,StackRoutines.clearStacks]

theorem moveScope_eval (rf : Fin 11 → Bool) (width modulus master shape out clause : List Bool) :
    Eval moveScope (3*clause.length+3) (data rf width modulus master shape out [] [] clause [] [])
      (data (readRegs rf 8 9 none) width modulus master shape out [] [] [] [] clause.reverse) := by
  have h := SubexponentialSAT.SubexpScanPrimitives.transfer_eval
    (data rf width modulus master shape out [] [] clause [] []) 73 47 8 9 (by decide) (by decide)
  convert h using 1
  · simp [data, tapes]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> simp [data,tapes,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks]

abbrev process : Cmd 11 80 := .seq fetch (.seq prepareScope (.seq extract
  (.seq clearEll (.seq moveScope MarkedFrame.command))))

def processCost (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (i : Fin clauses.length) : ℕ :=
  23*(Encoding.encodeList id clauses).length+SubexpScopeProducer.budget [true] (codes i)+
    8*(scopeBits (codes i)).length+51

theorem process_eval (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i)) (i : Fin clauses.length)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) :
    ∃ n ≤ processCost clauses codes i, ∃ rf', rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval process n
        (data rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) [] [] [] [])
        (data rf' width modulus (Encoding.encodeList id clauses) shape
          (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBits (codes i)) out) [] [] [] [] []) := by
  obtain ⟨nf,hnf,r1,hf⟩ := fetch_eval clauses i rf width modulus shape out
  rw [hc] at hf
  have hp := prepareScope_eval r1 width modulus (Encoding.encodeList id clauses) shape out
    (Encoding.encodeList Encoding.encodeNat (codes i))
  obtain ⟨ns,hns,r2,hs⟩ := extract_eval (codes i) width modulus (Encoding.encodeList id clauses) shape out
  have he := clearEll_eval r2 width modulus (Encoding.encodeList id clauses) shape out (scopeBits (codes i))
  have hm := moveScope_eval (readRegs r2 8 9 none) width modulus (Encoding.encodeList id clauses) shape out (scopeBits (codes i))
  let a := data (readRegs (readRegs r2 8 9 none) 8 9 none) width modulus (Encoding.encodeList id clauses) shape out [] [] [] []
    (scopeBits (codes i)).reverse
  obtain ⟨z,hz,h47,h48,h8,h9,h10,hframe⟩ := MarkedFrame.command_eval a (scopeBits (codes i)) (by simp [a,data,tapes])
  have hz' : z=data z.regs width modulus (Encoding.encodeList id clauses) shape
      (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBits (codes i)) out) [] [] [] [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      by_cases hj47 : j=47
      · subst j; simpa [data,tapes] using h47
      by_cases hj48 : j=48
      · subst j; simpa [a,data,tapes] using h48
      rw [hframe j hj47 hj48]
      simp [a,data,tapes,hj47,hj48]
  rw [hz'] at hz
  refine ⟨_,?_,z.regs,h8,h9,h10,hf.seq (hp.seq (hs.seq (he.seq (hm.seq hz))))⟩
  unfold processCost
  omega

abbrev clearIndex : Cmd 11 80 := .call (StackRoutines.clearProgram 49 8 9)

theorem clearIndex_eval (rf : Fin 11 → Bool) (width modulus master shape out index : List Bool) :
    Eval clearIndex (2*index.length+3)
      (data rf width modulus master shape out index [] [] [] [])
      (data (readRegs rf 8 9 none) width modulus master shape out [] [] [] [] []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (49 : Fin 80) (8 : Fin 11) 9
    (data rf width modulus master shape out index [] [] [] [])
  convert h using 1
  · simp [data, tapes]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext j; fin_cases j <;> simp [data,tapes,StackRoutines.clearStacks]

abbrev popFlag : Cmd 11 80 := .base (.atom (.pop 50 8 9))

theorem popFlag_eval (rf : Fin 11 → Bool) (width modulus master shape out index : List Bool) (flag : Bool) :
    Eval popFlag 1 (data rf width modulus master shape out index [flag] [] [] [])
      (data (readRegs rf 8 9 (some flag)) width modulus master shape out index [] [] [] []) := by
  have h := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (50 : Fin 80) (8 : Fin 11) 9)
    (data rf width modulus master shape out index [flag] [] [] []))
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> simp [data,tapes,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]

abbrev optional : Cmd 11 80 := .seq popFlag (.ite 8 process (.seq clearIndex MarkedFrame.fix))

def appended {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (mark : Option (Fin clauses.length)) (out : List Bool) : List Bool :=
  match mark with
  | none => out
  | some i => SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBits (codes i)) out

def optionalCost (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (mark : Option (Fin clauses.length)) (index : List Bool) : ℕ :=
  2*index.length+10+(mark.map (processCost clauses codes)).getD 0

theorem optional_eval (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (mark : Option (Fin clauses.length)) (index : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (rf : Fin 11 → Bool) (width modulus shape out : List Bool) :
    ∃ n ≤ optionalCost clauses codes mark index, ∃ rf', rf' 8=false ∧ rf' 9=true ∧ rf' 10=false ∧
      Eval optional n
        (data rf width modulus (Encoding.encodeList id clauses) shape out index [mark.isSome] [] [] [])
        (data rf' width modulus (Encoding.encodeList id clauses) shape (appended (clauses := clauses) codes mark out) [] [] [] [] []) := by
  cases mark with
  | none =>
      have hp := popFlag_eval rf width modulus (Encoding.encodeList id clauses) shape out index false
      let r := readRegs rf 8 9 (some false)
      have hc := clearIndex_eval r width modulus (Encoding.encodeList id clauses) shape out index
      let a := data (readRegs r 8 9 none) width modulus (Encoding.encodeList id clauses) shape out [] [] [] [] []
      have hf := MarkedFrame.fix_eval a
      refine ⟨1+((2*index.length+3)+3)+1,by simp [optionalCost]; omega,(MarkedFrame.fixed a).regs,?_,?_,?_,?_⟩
      · simp [MarkedFrame.fixed]
      · simp [MarkedFrame.fixed]
      · simp [MarkedFrame.fixed]
      · exact hp.seq (Eval.ite_false (by simp [data,readRegs]) (hc.seq hf))
  | some i =>
      have hi := hindex i rfl
      subst index
      have hp := popFlag_eval rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) true
      obtain ⟨n,hn,r,h8,h9,h10,he⟩ := process_eval clauses codes hc i (readRegs rf 8 9 (some true)) width modulus shape out
      refine ⟨1+n+1,?_,r,h8,h9,h10,?_⟩
      · simp [optionalCost]; omega
      · exact hp.seq (Eval.ite_true (by simp [data,readRegs]) he)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
