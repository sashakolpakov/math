import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingEmpty
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryAccepted

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

 theorem marked_packingSpare (a : Data) (hs : PackingSpare a) : PackingSpare (markedInput a) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (markedInput_frame a 684 (by decide) (by decide) (by decide)).trans hs.1
  · exact (markedInput_frame a 133 (by decide) (by decide) (by decide)).trans hs.2.1
  · exact (markedInput_frame a 135 (by decide) (by decide) (by decide)).trans hs.2.2.1
  · exact (markedInput_frame a 136 (by decide) (by decide) (by decide)).trans hs.2.2.2.1
  · intro i
    exact (markedInput_frame a _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)).trans (hs.2.2.2.2 i)

 theorem accepted_packingSpare (a : Data) (hs : PackingSpare a) : PackingSpare (unmarkedInput a) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (unmarkedInput_frame a 684 (by decide) (by decide)).trans hs.1
  · exact (unmarkedInput_frame a 133 (by decide) (by decide)).trans hs.2.1
  · exact (unmarkedInput_frame a 135 (by decide) (by decide)).trans hs.2.2.1
  · exact (unmarkedInput_frame a 136 (by decide) (by decide)).trans hs.2.2.2.1
  · intro i
    exact (unmarkedInput_frame a _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)).trans (hs.2.2.2.2 i)

/-- Entry facts come from the reusable blank workspace and immutable sources;
no prepared scope or ring cache is supplied to the marked callback. -/
theorem marked_entry (q : LeafQueryFrontend.Query) (a : Data) (hc : CleanWork a)
    (hs : Sources q a) (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse) :
    Eval markInput (10*(a.stacks 321).length+10) a (markedInput a) ∧
    q.Ready (markedInput a) ∧ q.OutputEmpty (markedInput a) ∧ PackingSpare (markedInput a) := by
  exact ⟨markInput_eval a (hc _ (by decide) (by decide)) (hc _ (by decide) (by decide)),
    marked_ready q a hc hs hm href,marked_outputs_empty a hc,
    marked_packingSpare a (cleanWork_packingSpare a hc)⟩

theorem accepted_entry (q : LeafQueryFrontend.Query) (a : Data) (hc : CleanWork a)
    (hs : Sources q a) (hm : q.mark=none) (hindex : q.index=[false]) :
    Eval noMarkInput 3 a (unmarkedInput a) ∧
    q.Ready (unmarkedInput a) ∧ q.OutputEmpty (unmarkedInput a) ∧ PackingSpare (unmarkedInput a) := by
  exact ⟨noMarkInput_eval a,accepted_ready q a hc hs hm hindex,
    accepted_outputs_empty a hc,accepted_packingSpare a (cleanWork_packingSpare a hc)⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
