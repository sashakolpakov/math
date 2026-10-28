import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch

namespace OAI.Algorithms

/-! Fixed finite-control generation in the exact irreducible-search order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData

/-- The depth is stack data; the ordered Cartesian body is fixed. -/
abbrev powerLoop : Cmd 10 9 :=
  .while 9 (.seq SubexpOrderedTupleStep.step readDepth)
abbrev powerCmd : Cmd 10 9 := .seq readDepth powerLoop

def powerCost (alphabet : Records) : ℕ → Records → ℕ
  | 0, _ => 2
  | n + 1, rows => SubexpOrderedTupleStep.stepCost rows alphabet +
      powerCost alphabet n (orderedCartesian rows alphabet) + 2

theorem powerCmd_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ powerCost alphabet depth.length rows ∧
      Ready alphabet (orderedRows alphabet depth.length rows) [] false next ∧
      Eval powerCmd n a next := by
  induction depth generalizing rows guard a with
  | nil =>
      let b := readDepthState a
      have hb : Ready alphabet rows [] false b := by
        rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
        simp [Ready, outerInvariant, b, readRegs,
          h1,h3,h4,h6,h7,h8,h0,h2,h5]
      refine ⟨2, b, le_rfl, hb, ?_⟩
      exact (readDepth_eval a).seq (Eval.while_false hb.1.2.2.2.2.2.2)
  | cons bit depth ih =>
      let b := readDepthState a
      have hb : Ready alphabet rows depth true b := by
        rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
        simp [Ready, outerInvariant, b, readRegs,
          h1,h3,h4,h6,h7,h8,h0,h2,h5]
      obtain ⟨n, c, hn, hc, ht⟩ := SubexpOrderedTupleStep.step_eval alphabet rows depth true b hb
      obtain ⟨m, d, hm, hd, hr⟩ := ih (orderedCartesian rows alphabet) true c hc
      cases hr with
      | @seq first second k l x y z hp hl =>
          refine ⟨1 + (n + k + l + 1), d, ?_, hd, ?_⟩
          · simp only [List.length_cons, powerCost]
            omega
          · exact (readDepth_eval a).seq
              (Eval.while_true hb.1.2.2.2.2.2.2 (ht.seq hp) hl)


abbrev generateCmd : Cmd 10 9 := .seq initCmd powerCmd
def program := StructuredCalls.compiled generateCmd 1 0

theorem program_runsIn (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ next, Ready alphabet (orderedRows alphabet depth.length [[]]) [] false next ∧
      RunsIn program (powerCost alphabet depth.length [[]] + 9)
        (a.withPC (some program.entry)) (next.withPC none) := by
  obtain ⟨b,hb,hi⟩ := initCmd_eval alphabet depth guard a ha h0 h2 h5
  obtain ⟨n,next,hn,hs,he⟩ := powerCmd_eval alphabet [[]] depth guard b hb
  refine ⟨next,hs,8+n+1,by omega,?_⟩
  exact StructuredCalls.compiled_halt_trace (hi.seq he) 1 0

open SubexpEnumerationPayload SubexpTupleRefinement

def alphabet : Records := (QuarticSearch.elements 3).map (scalarCode 3).block

def input (d : ℕ) : State 10 9 :=
  ⟨fun _ => false, fun i =>
    if i = 1 then ProgramEncoding.encodeRecords alphabet
    else if i = 8 then List.replicate d false else []⟩

def cost (d : ℕ) : ℕ := powerCost alphabet d [[]] + 9

theorem selected_runsIn (d : ℕ) :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords
        ((IrreducibleSearch.candidates d).map (encodeTuple (scalarCode 3))) ∧
      next.stacks 8 = [] ∧
      RunsIn program (cost d)
        ((input d).withPC (some program.entry)) (next.withPC none) := by
  have ha : outerInvariant alphabet (List.replicate d false) false (input d) := by
    simp [outerInvariant, input]
  obtain ⟨next, hn, hr⟩ := program_runsIn alphabet (List.replicate d false) false
    (input d) ha (by simp [input]) (by simp [input]) (by simp [input])
  refine ⟨next, ?_, hn.1.2.2.2.2.2.1, ?_⟩
  · have h := hn.2.1
    simpa only [List.length_replicate, alphabet, orderedRows_encoded,
      IrreducibleSearch.candidates] using h
  · simpa only [List.length_replicate, cost] using hr

theorem selected_primitive_runsIn (d : ℕ) :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords
        ((IrreducibleSearch.candidates d).map (encodeTuple (scalarCode 3))) ∧
      next.stacks 8 = [] ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * cost d)
        (primitiveCfg program ((input d).withPC (some program.entry)))
        (primitiveCfg program (next.withPC none)) := by
  obtain ⟨next, hout, hdepth, hr⟩ := selected_runsIn d
  exact ⟨next, hout, hdepth, primitive_execution program hr⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

end OAI.Algorithms
