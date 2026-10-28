import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryPlan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendSemantics

namespace OAI.Algorithms

/-! The physical branch metadata uses the same original-ID high set as the
actual addressed packing problem. These lemmas add no scope or mask promise. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram LeafParametersProgram

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))

abbrev queryHigh := NodeConcrete.planHigh (Query.packingProblem q k hg)

theorem query_forward :
    q.forward=List.ofFn (fun v : Fin (Query.packingProblem q k hg).n=>
      decide (v∈queryHigh q k hg)) := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn,Query.packingProblem] using q.forward_length
  · intro i hi hj
    have hn : i < (Query.packingProblem q k hg).n := by
      simpa only [List.length_ofFn] using hj
    have h := NodeConcrete.planHigh_mask (Query.packingProblem q k hg) ⟨i,hn⟩
    change q.forward.getD i false=decide ((⟨i,hn⟩ : Fin (Query.packingProblem q k hg).n)∈queryHigh q k hg) at h
    rw [List.getD_eq_getElem _ _ hi] at h
    simpa only [List.getElem_ofFn] using h

theorem query_descending_mask :
    descendingMask (queryHigh q k hg)=q.forward.reverse := by
  rw [descendingMask_eq,←query_forward q k hg]

theorem query_high_count :
    Branches.trueCount q.forward.reverse=(queryHigh q k hg).card := by
  rw [←query_descending_mask q k hg]
  exact descendingMask_count _

theorem query_physical_bits (words : List (List Bool))
    (hshape : words.map List.length=List.replicate (Branches.trueCount q.forward.reverse) 1)
    (r : Fin (2^(queryHigh q k hg).card))
    (hr : CounterPrograms.value words.flatten=r.val) :
    (Restriction.zeroMerge q.forward.reverse words.flatten).reverse=
      List.ofFn (HighIncidence.glue (queryHigh q k hg)
        (Rank.highEquiv (Order.highOrder (queryHigh q k hg)) r) (fun _=>false)) := by
  have hs : words.map List.length=List.replicate (queryHigh q k hg).card 1 := by
    simpa only [query_high_count q k hg] using hshape
  have h := physicalBits_rank (queryHigh q k hg) words hs r hr
  simpa only [physicalBits,query_descending_mask q k hg] using h

theorem query_physical_count
    (hashes : List (SparseRow (Fin (Query.packingProblem q k hg).n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin (Query.packingProblem q k hg).n)))
    (words : List (List Bool))
    (hshape : words.map List.length=List.replicate (Branches.trueCount q.forward.reverse) 1) :
    NodeSemantics.ternaryFixedHighCount (queryHigh q k hg)
      (fun v=>(Restriction.zeroMerge q.forward.reverse words.flatten).reverse.getD v.val.val false)
      hashes marked clause =
      rankValue (queryHigh q k hg) hashes marked clause (CounterPrograms.value words.flatten) := by
  have hs : words.map List.length=List.replicate (queryHigh q k hg).card 1 := by
    simpa only [query_high_count q k hg] using hshape
  have h := physical_count (queryHigh q k hg) hashes marked clause words hs
  simpa only [physicalBits,query_descending_mask q k hg] using h

theorem query_rankSum_fullCount
    (hashes : List (SparseRow (Fin (Query.packingProblem q k hg).n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin (Query.packingProblem q k hg).n))) :
    LeafBranchProgram.rankSum (rankValue (queryHigh q k hg) hashes marked clause)
      0 (2^(Branches.trueCount q.forward.reverse))=fullCount hashes marked clause := by
  rw [query_high_count q k hg]
  exact rankSum_fullCount _ _ _ _

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
