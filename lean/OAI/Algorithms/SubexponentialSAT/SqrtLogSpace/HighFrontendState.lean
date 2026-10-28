import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontState

/-! Complete physical preparation facts derived from the actual marked and
unmarked frontend command outputs. No precomputed FrontState is supplied. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls SqrtLog

/-- The exact native output has every packing-stage field, including spare
words and canonical parameter lengths. Its base is after reference staging. -/
theorem command_front_state (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) (he : Eval (command k) steps a b) :
    ∃ l w, LeafProgram.Query.FrontState q k
      (LeafProgram.Query.markedInput (project a)) (project b) l w := by
  obtain ⟨hmark,hready,hempty,hspare⟩ :=
    LeafProgram.Query.marked_entry q (project a) hc hs hm href
  obtain ⟨nf,bf,l,w,hfront,_,hf⟩ := LeafProgram.Query.front_state q k
    (LeafProgram.Query.markedInput (project a)) hv hready hempty hspare
  have hwhole : Eval (LeafProgram.Query.markedFrontend k)
      (10 * ((project a).stacks 321).length + 10 + nf) (project a) bf := by
    unfold LeafProgram.Query.markedFrontend
    exact hmark.seq hfront
  have htcompiled : Trace (compiled (LeafProgram.Query.markedFrontend k) 321 338)
      (10 * ((project a).stacks 321).length + 10 + nf + 1)
      ((project a).withPC (some (compiled (LeafProgram.Query.markedFrontend k) 321 338).entry))
      (bf.withPC none) :=
    compiled_halt_trace hwhole 321 338
  have htlocal : Trace (localProgram k) (10 * ((project a).stacks 321).length + 10 + nf + 1)
      ((project a).withPC (some (localProgram k).entry)) (bf.withPC none) := by
    simpa only [localProgram] using htcompiled
  have hev : Eval (command k) _ a (result a bf) :=
    eval_call_from_state (localProgram k) id stackMap a
      Function.injective_id (Fin.castAdd_injective _ _) htlocal
  have hb := SubexpPrimeProgram.eval_result_unique he hev 321 338
  refine ⟨l,w,?_⟩
  rw [hb,project_result]
  exact hf

/-- The unmarked final query has the same fully computed physical packing
input, with its base after actual false-flag staging. -/
theorem accepted_command_front_state (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) (he : Eval (acceptedCommand k) steps a b) :
    ∃ l w, LeafProgram.Query.FrontState q k
      (LeafProgram.Query.unmarkedInput (project a)) (project b) l w := by
  obtain ⟨hmark,hready,hempty,hspare⟩ :=
    LeafProgram.Query.accepted_entry q (project a) hc hs hm hindex
  obtain ⟨nf,bf,l,w,hfront,_,hf⟩ := LeafProgram.Query.front_state q k
    (LeafProgram.Query.unmarkedInput (project a)) hv hready hempty hspare
  have hwhole : Eval (acceptedLocalCommand k) (3 + nf) (project a) bf := by
    unfold acceptedLocalCommand
    exact hmark.seq hfront
  have htcompiled : Trace (compiled (acceptedLocalCommand k) 700 338) (3 + nf + 1)
      ((project a).withPC (some (compiled (acceptedLocalCommand k) 700 338).entry))
      (bf.withPC none) :=
    compiled_halt_trace hwhole 700 338
  have htlocal : Trace (acceptedLocalProgram k) (3 + nf + 1)
      ((project a).withPC (some (acceptedLocalProgram k).entry)) (bf.withPC none) := by
    simpa only [acceptedLocalProgram] using htcompiled
  have hev : Eval (acceptedCommand k) _ a (result a bf) :=
    eval_call_from_state (acceptedLocalProgram k) id stackMap a
      Function.injective_id (Fin.castAdd_injective _ _) htlocal
  have hb := SubexpPrimeProgram.eval_result_unique he hev 700 338
  refine ⟨l,w,?_⟩
  rw [hb,project_result]
  exact hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
