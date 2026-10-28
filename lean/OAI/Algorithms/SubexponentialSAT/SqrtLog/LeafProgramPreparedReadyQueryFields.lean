import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedPersistent
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPreparationState

namespace OAI.Algorithms

/-! Query masters survive the executed frontend, packing and arithmetic.
The generated row count is read from the actual frontend output. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

structure QueryFields (q : LeafQueryFrontend.Query) (a : Factor.Data) : Prop where
  clauses : a.stacks 700=Encoding.encodeList id q.clauses
  rows : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows
  count : a.stacks 704=List.replicate q.rows.length true
  index : a.stacks 705=q.index
  marked : a.stacks 706=[q.mark.isSome]
  modulus : a.stacks 707=q.modulus
  width : a.stacks 708=q.width

 theorem query_fields {q : LeafQueryFrontend.Query} {k : ℕ} {a : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k a hg W V L)
    (hr : q.Ready a) : QueryFields q p.out := by
  have frame (i : Fin 768) (hi : i∈([700,701,705,706,707,708] : List (Fin 768))) :
      p.out.stacks i=a.stacks i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      exact (p.arithmeticOutput.highFrame _ (by decide) (by decide) (by decide)).trans
        ((p.packingFrame _ (by decide) (by decide) (by decide)).trans
          (p.frontOutput.frame _ (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)))
  refine ⟨(frame 700 (by simp)).trans hr.1,(frame 701 (by simp)).trans hr.2.1,?_,
    (frame 705 (by simp)).trans hr.2.2.1,(frame 706 (by simp)).trans hr.2.2.2.1,
    (frame 707 (by simp)).trans hr.2.2.2.2.1,(frame 708 (by simp)).trans hr.2.2.2.2.2.1⟩
  exact (p.arithmeticOutput.highFrame _ (by decide) (by decide) (by decide)).trans
    ((p.packingFrame _ (by decide) (by decide) (by decide)).trans p.frontOutput.hashCount)

 theorem QueryFields.frame {q : LeafQueryFrontend.Query} {a b : Factor.Data}
    (h : QueryFields q a) (hf : PreparedSource.Persistent a b) : QueryFields q b := by
  exact ⟨(hf 700 (by decide)).trans h.clauses,(hf 701 (by decide)).trans h.rows,
    (hf 704 (by decide)).trans h.count,(hf 705 (by decide)).trans h.index,
    (hf 706 (by decide)).trans h.marked,(hf 707 (by decide)).trans h.modulus,
    (hf 708 (by decide)).trans h.width⟩

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
