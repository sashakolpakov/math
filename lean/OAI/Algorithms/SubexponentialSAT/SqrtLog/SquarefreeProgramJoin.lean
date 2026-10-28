import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramNat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeIndexEncoding

namespace OAI.Algorithms

/-! A single finite primitive program joins encoded sparse indices. Unary
exponents are added by scanning their fields; support bits are unioned by the
fixed OR scanner. The complete output is reversed for direct record emission. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev indexJoin : Cmd 5 3 :=
  .seq joinNat (.seq joinNat (.call maskUnionProgram))

def indexJoinProgram := compiled indexJoin 0 2

theorem indexJoin_eval {n : ℕ} (a b : Index (Fin n))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ final, Eval indexJoin (4*(a.u+b.u+a.z+b.z)+6*n+21)
      (maskData regs (encodeIndex a) (encodeIndex b) output)
      (maskData final [] [] ((encodeIndex (a.join b)).reverse ++ output)) := by
  obtain ⟨r1,h1⟩ := joinNat_eval regs a.u b.u
    (Encoding.encodeNat a.z ++ encodeMask a.vars)
    (Encoding.encodeNat b.z ++ encodeMask b.vars) output
  obtain ⟨r2,h2⟩ := joinNat_eval r1 a.z b.z (encodeMask a.vars) (encodeMask b.vars)
    ((Encoding.encodeNat (a.u+b.u)).reverse ++ output)
  obtain ⟨r3,h3⟩ := supportUnion_trace a.vars b.vars
    ((Encoding.encodeNat (a.z+b.z)).reverse ++
      ((Encoding.encodeNat (a.u+b.u)).reverse ++ output)) r2
  have h3' := Eval.call maskUnionProgram h3
  have he := h1.seq (h2.seq h3')
  have ht : (4*(a.u+b.u)+9)+((4*(a.z+b.z)+9)+(6*n+3)) =
      4*(a.u+b.u+a.z+b.z)+6*n+21 := by omega
  rw [ht] at he
  refine ⟨r3,?_⟩
  simpa [indexJoin,encodeIndex,Index.join,List.reverse_append,List.append_assoc] using he

/-- Actual primitive execution, with an exact count linear in key size. -/
theorem indexJoin_trace {n : ℕ} (a b : Index (Fin n))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ final, Trace indexJoinProgram (4*(a.u+b.u+a.z+b.z)+6*n+22)
      ((maskData regs (encodeIndex a) (encodeIndex b) output).withPC
        (some indexJoinProgram.entry))
      ((maskData final [] [] ((encodeIndex (a.join b)).reverse ++ output)).withPC none) := by
  obtain ⟨final,h⟩ := indexJoin_eval a b regs output
  exact ⟨final,by simpa [indexJoinProgram,Nat.add_assoc] using compiled_halt_trace h 0 2⟩

theorem indexJoin_cost_le {n t J : ℕ} (a b : Index (Fin n))
    (ha : a.Kept t J) (hb : b.Kept t J) :
    4*(a.u+b.u+a.z+b.z)+6*n+22 ≤ 8*(t+J)+6*n+22 := by
  obtain ⟨hau,haz⟩ := ha
  obtain ⟨hbu,hbz⟩ := hb
  omega

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
