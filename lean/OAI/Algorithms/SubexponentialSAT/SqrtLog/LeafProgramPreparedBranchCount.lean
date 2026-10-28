import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramShiftSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCountSource

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def descendingMask (H : Finset (Fin n)) : List Bool :=
  (Order.coordinates n).map (fun v=>decide (v∈H))

theorem descendingMask_eq (H : Finset (Fin n)) :
    descendingMask H=(List.ofFn (fun v : Fin n=>decide (v∈H))).reverse :=
  Order.coordinates_stream n _

theorem descendingMask_count (H : Finset (Fin n)) :
    Branches.trueCount (descendingMask H)=H.card := by
  have he : ((descendingMask H).filter id).length=(Order.highCoordinates H).length := by
    unfold descendingMask Order.highCoordinates
    rw [List.filter_map]
    simp
  exact he.trans (Order.highCoordinates_length H)

def physicalBits (H : Finset (Fin n)) (words : List (List Bool)) : List Bool :=
  (Restriction.zeroMerge (descendingMask H) words.flatten).reverse

theorem zeroMerge_high (H : Finset (Fin n)) (a : H → Bool) :
    (Restriction.zeroMerge (descendingMask H)
      (List.ofFn (fun i=>a (Order.highOrder H i)))).reverse =
      List.ofFn (HighIncidence.glue H a (fun _=>false)) := by
  let x := HighIncidence.glue H a (fun _=>false)
  have hhigh : List.ofFn (fun i=>a (Order.highOrder H i))=(Order.highCoordinates H).map x := by
    rw [←Order.highOrder_stream]
    congr 1
    funext i
    simp [x,HighIncidence.glue,(Order.highOrder H i).property]
  rw [hhigh]
  unfold descendingMask Order.highCoordinates
  rw [Restriction.zeroMerge_map]
  have hx : (fun v=>if decide (v∈H) then x v else false)=x := by
    funext v
    by_cases hv : v∈H <;> simp [hv,x,HighIncidence.glue]
  rw [hx,Order.coordinates_stream,List.reverse_reverse]

private theorem flatten_singletons (xs : List Bool) :
    (xs.map (fun b=>[b])).flatten=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]

theorem physicalBits_rank (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1)
    (r : Fin (2^H.card)) (hr : CounterPrograms.value words.flatten=r.val) :
    physicalBits H words=List.ofFn (HighIncidence.glue H
      (Rank.highEquiv (Order.highOrder H) r) (fun _=>false)) := by
  have hw := Rank.tuple_of_rank words hshape r hr
  have hbits : words.flatten=List.ofFn (fun i : Fin H.card=>
      (Rank.highEquiv (Order.highOrder H) r) (Order.highOrder H i)) := by
    rw [hw,flatten_singletons]
    congr 1
    funext i
    simp [Rank.highEquiv,Rank.reindex,Rank.assignment]
  unfold physicalBits
  rw [hbits]
  exact zeroMerge_high H _

theorem physicalBits_high (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1)
    (r : Fin (2^H.card)) (hr : CounterPrograms.value words.flatten=r.val) (v : H) :
    (physicalBits H words).getD v.val.val false=Rank.highEquiv (Order.highOrder H) r v := by
  rw [physicalBits_rank H words hshape r hr]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [HighIncidence.glue,v.property]

theorem flattened_length (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) : words.flatten.length=H.card := by
  rw [List.length_flatten,hshape]
  simp

theorem physical_rank_lt (H : Finset (Fin n)) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) :
    CounterPrograms.value words.flatten < 2^H.card := by
  simpa only [flattened_length H words hshape] using
    ExecCNFTupleOdometer.value_lt_power_length words.flatten

def rankValue (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (r : ℕ) : ℕ :=
  if hr:r < 2^H.card then NodeSemantics.ternaryFixedHighCount H
    (Rank.highEquiv (Order.highOrder H) ⟨r,hr⟩) hashes marked clause else 0

def fullCount (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) : ℕ :=
  ∑ x : Fin n → Bool, if NodeSemantics.ternaryAccepted hashes marked clause x then 1 else 0

theorem rankValue_at (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (r : Fin (2^H.card)) :
    rankValue H hashes marked clause r.val=NodeSemantics.ternaryFixedHighCount H
      (Rank.highEquiv (Order.highOrder H) r) hashes marked clause := by
  simp only [rankValue,dite_eq_left r.isLt]

theorem physical_count (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate H.card 1) :
    NodeSemantics.ternaryFixedHighCount H
      (fun v=>(physicalBits H words).getD v.val.val false) hashes marked clause =
      rankValue H hashes marked clause (CounterPrograms.value words.flatten) := by
  let r : Fin (2^H.card) := ⟨_,physical_rank_lt H words hshape⟩
  have he : (fun v : H=>(physicalBits H words).getD v.val.val false)=
      Rank.highEquiv (Order.highOrder H) r := by
    funext v
    exact physicalBits_high H words hshape r rfl v
  rw [he]
  exact (rankValue_at H hashes marked clause r).symm

theorem rankSum_fullCount (H : Finset (Fin n)) (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    LeafBranchProgram.rankSum (rankValue H hashes marked clause) 0 (2^H.card)=
      fullCount hashes marked clause := by
  apply LeafBranchProgram.rankSum_original H (Order.highOrder H)
    (NodeSemantics.ternaryAccepted hashes marked clause)
  intro r
  exact rankValue_at H hashes marked clause r

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
