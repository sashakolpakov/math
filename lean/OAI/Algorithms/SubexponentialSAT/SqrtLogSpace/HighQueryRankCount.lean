import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryPlan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget

/-! The actual produced factor constructor and physical high odometer use
one source predicate and one descending rank order. Arithmetic witnesses and
interpolation nodes introduce no additional acceptance condition. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryRankCount

open OAI SqrtLog LeafProgram LeafParametersProgram
open PreparedSource PreparedBranchCount NodeConcrete
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- The freshly computed physical high mask is the addressed packing high
set, including the empty high set. The ambient dimension is unchanged. -/
theorem query_high (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    NodeConcrete.planHigh (Query.packingProblem q k hg) = HighMarkedFrontend.highSet q := by
  classical
  have hf : q.forward = List.ofFn (fun v : Fin (BinaryArithmetic.toNat q.ambient) =>
      decide (v ∈ HighMarkedFrontend.highSet q)) := by
    unfold LeafQueryFrontend.Query.forward
    rw [HighMarkedFrontend.physical_high_mask]
    change (descendingMask (HighMarkedFrontend.highSet q)).reverse = _
    rw [descendingMask_eq,List.reverse_reverse]
  ext v
  apply decide_eq_decide.mp
  rw [← NodeConcrete.planHigh_mask (Query.packingProblem q k hg) v]
  change q.forward.getD v.val false = decide (v ∈ HighMarkedFrontend.highSet q)
  rw [hf]
  rw [List.getD_eq_getElem _ _ (by simpa [Query.packingProblem] using v.isLt)]
  simp only [List.getElem_ofFn, decide_eq_decide]
  rw [show (⟨v.val, by simpa [Query.packingProblem] using v.isLt⟩ :
    Fin (BinaryArithmetic.toNat q.ambient)) = v from Fin.ext rfl]
  rfl

section Native

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3 ^ (m.val 34))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv J hJ source hsource

local notation "hashes" => List.map
  (fun terms => List.map
    (fun term => (Prod.snd term,HashInputProgram.Expansion.originalClause source (Prod.fst term))) terms)
  (castRows (congrArg List.length hsource) (LeafQueryFrontend.Query.rows q))

/-- These are the literal original clauses and row coefficients of the
actual constructor, with only the proved finite-index transport. -/
theorem native_source_hashes : sourceHashes spec = hashes := rfl

/-- The actual native fixed-high answer is precisely the integer summand
used by the high-assignment accumulator; no coefficient or bit is tested. -/
theorem native_rank_count (H : Finset (Fin s.n)) (rank : Fin (2 ^ H.card)) :
    NodeSemantics.ternaryFixedHighCount H (Rank.highEquiv (Order.highOrder H) rank)
      (sourceHashes spec) (spec).marked (spec).markedClause =
    rankValue H hashes q.mark.isSome (source[markIndex q]?.getD []) rank.val := by
  change NodeSemantics.ternaryFixedHighCount H (Rank.highEquiv (Order.highOrder H) rank)
    hashes q.mark.isSome (source[markIndex q]?.getD []) = _
  exact (rankValue_at H hashes q.mark.isSome (source[markIndex q]?.getD []) rank).symm

/-- The literal reversed zero-merge vector read by the machine gives the
same summand, including the unique rank when there are no high coordinates. -/
theorem native_physical_count (H : Finset (Fin s.n))
    (tuple : List (List Bool)) (hshape : tuple.map List.length = List.replicate H.card 1) :
    NodeSemantics.ternaryFixedHighCount H
      (fun v => (physicalBits H tuple).getD v.val.val false)
      (sourceHashes spec) (spec).marked (spec).markedClause =
    rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])
      (CounterPrograms.value tuple.flatten) := by
  change NodeSemantics.ternaryFixedHighCount H
    (fun v => (physicalBits H tuple).getD v.val.val false)
    hashes q.mark.isSome (source[markIndex q]?.getD []) = _
  exact physical_count H hashes q.mark.isSome (source[markIndex q]?.getD []) tuple hshape

/-- The actual decoder's ascending ambient vector determines exactly the
same descending high-coordinate rank. Low coordinates are not counted twice. -/
theorem native_decoded_count (H : Finset (Fin s.n)) (rank : Fin (2 ^ H.card))
    (bits : List Bool)
    (hbits : bits = List.ofFn (HighIncidence.glue H
      (Rank.highEquiv (Order.highOrder H) rank) (fun _ => false))) :
    NodeSemantics.ternaryFixedHighCount H (fun v => bits.getD v.val.val false)
      (sourceHashes spec) (spec).marked (spec).markedClause =
    rankValue H hashes q.mark.isSome (source[markIndex q]?.getD []) rank.val := by
  have hhigh : (fun v : H => bits.getD v.val.val false) =
      Rank.highEquiv (Order.highOrder H) rank := by
    funext v
    rw [hbits,List.getD_eq_getElem _ _ (by simp)]
    simp [HighIncidence.glue,v.property]
  rw [hhigh]
  exact native_rank_count s m ht hd words hc M cache half e hp hfield q hv J hJ
    source hsource H rank

/-- Summing exactly the attained rank interval gives the full ambient source
count. This is a proof-side sum; the executable loop retains a binary word. -/
theorem native_rank_sum (H : Finset (Fin s.n)) :
    LeafBranchProgram.rankSum
      (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])) 0 (2 ^ H.card) =
    fullCount (sourceHashes spec) (spec).marked (spec).markedClause := by
  change LeafBranchProgram.rankSum
    (rankValue H hashes q.mark.isSome (source[markIndex q]?.getD [])) 0 (2 ^ H.card) =
    fullCount hashes q.mark.isSome (source[markIndex q]?.getD [])
  exact rankSum_fullCount H hashes q.mark.isSome (source[markIndex q]?.getD [])

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryRankCount
