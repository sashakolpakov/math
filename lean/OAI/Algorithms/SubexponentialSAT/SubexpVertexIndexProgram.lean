import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram

namespace OAI.Algorithms

/-! A fixed generator for exactly the vertex indices below unary D. -/
namespace SubexponentialSAT.SubexpVertexIndexProgram

open BitProgram StructuredCalls

abbrev unary (n : ℕ) := List.replicate n true

theorem earlierRows_eq (k n : ℕ) :
    Subexp.DimensionProgram.earlierRows k n = (List.range' k n).reverse.map unary := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      simp [Subexp.DimensionProgram.earlierRows,List.range'_succ,ih,List.reverse_cons]

abbrev command : Cmd 5 5 := .seq (Subexp.TupleProgram.pushConst 3 2 false)
  Subexp.DimensionProgram.enumerate

theorem command_eval (D : ℕ) (a : State 5 5)
    (h0 : a.stacks 0 = unary D) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Eval command (6*D^2+10*D+4) a b ∧
      Subexp.DimensionProgram.Ready D [] ((List.range' 0 D).reverse.map unary) b := by
  let c := Subexp.TupleProgram.pushedState 3 2 false a
  have hc : Subexp.DimensionProgram.Ready 0 (unary D) [] c := by
    simp [Subexp.DimensionProgram.Ready,c,
      h0,h1,h2,h3,h4,ProgramEncoding.encodeRecords,Encoding.encodeList]
  obtain ⟨b,hb,_,he⟩ := Subexp.DimensionProgram.enumerate_eval 0 (unary D) [] c hc
  have h := (Subexp.TupleProgram.pushConst_eval 3 2 false a).seq he
  refine ⟨b,?_,?_⟩
  · convert h using 1
    simp [Subexp.DimensionProgram.loopCost_eq]
    ring
  · simpa [earlierRows_eq] using hb

abbrev program : Program 5 5 (size command+1) := compiled command 0 3

theorem program_trace (D : ℕ) (a : State 5 5)
    (h0 : a.stacks 0 = unary D) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h4 : a.stacks 4 = []) :
    ∃ b, Trace program (6*D^2+10*D+5) (a.withPC (some program.entry)) (b.withPC none) ∧
      Subexp.DimensionProgram.Ready D [] ((List.range' 0 D).reverse.map unary) b := by
  obtain ⟨b,he,hb⟩ := command_eval D a h0 h1 h2 h3 h4
  exact ⟨b,by simpa [Nat.add_assoc] using compiled_halt_trace he 0 3,hb⟩

end SubexponentialSAT.SubexpVertexIndexProgram

end OAI.Algorithms
