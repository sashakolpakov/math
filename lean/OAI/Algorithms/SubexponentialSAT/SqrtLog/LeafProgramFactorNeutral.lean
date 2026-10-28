import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorRecord

namespace OAI.Algorithms

/-! The neutral IDs generated for uncovered free variables are consumed by
the real dispatcher and skipped; they are never looked up as hash rows. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

theorem callback_neutral_eval (a : Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701=Encoding.encodeList id rows)
    (hclauses : a.stacks 700=Encoding.encodeList id clauses)
    (hcount : a.stacks 704=List.replicate rows.length true)
    (hmark : a.stacks 705=Encoding.encodeNat mark)
    (hflag : a.stacks 706=[marked])
    (hfactor : a.stacks 149=(Encoding.encodeNat factor).reverse)
    (hwork : ∀ i ∈ FactorDispatch.scratch,a.stacks i=[])
    (hvalid : marked=true → mark < clauses.length)
    (hhash : ¬factor < rows.length)
    (hmarked : (marked && decide (factor=rows.length))=false) :
    ∃ k b,k ≤ 9*(a.stacks 149).length+14+
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval callback k a b ∧ b.stacks=Function.update a.stacks 149 [] ∧
      b.regs 13=false ∧ b.regs 14=true ∧ b.regs 15=false := by
  obtain ⟨kd,rd,hkd,hd,h5,h6,h7⟩ := FactorDispatch.command_eval a rows clauses marked mark factor
    hrows hclauses hcount hmark hflag hfactor hwork hvalid
  let d := FactorDispatch.finished a rd rows clauses marked mark factor
  have hd5 : d.regs 5=false := by
    rw [FactorDispatch.finished_role_hash,h5]
    exact decide_eq_false hhash
  have hd6 : d.regs 6=false := by
    rw [FactorDispatch.finished_role_marked,h6,hmarked]
  have hp : LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor=[] := by
    simp only [LeafFactorDispatchProgram.selectedPayload,ite_eq_right hhash,hmarked,Bool.false_eq_true,ite_false]
  have hs : d.stacks=a.stacks := by
    rw [FactorDispatch.finished_stacks a rd rows clauses marked mark factor hrows hclauses hcount hmark hwork,hp]
    simpa only [hwork 154 (by simp [FactorDispatch.scratch])] using
      Function.update_eq_self (154 : Fin 768) a.stacks
  have hc := choose_neutral_eval d hd5 hd6
  have hf := callbackFinish_eval d
  refine ⟨kd+(2+(2*(d.stacks 149).length+6)),callbackFinished d,?_,hd.seq (hc.seq hf),?_,
    callbackFinished_tag d,callbackFinished_present d,callbackFinished_found d⟩
  · rw [hs]
    omega
  · rw [callbackFinished_stacks,hs]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
