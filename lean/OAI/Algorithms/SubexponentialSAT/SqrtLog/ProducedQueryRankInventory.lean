import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankSchedule

namespace OAI.Algorithms

/-! The literal native incidence list and the actual produced head tables
share the same matrix rank bound, in their emitted order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank
open LeafHeadSetupProgram

def addressPair (p : Problem) (i : Fin p.incidences) : ℕ × ℕ :=
  (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask).get i

@[simp] theorem addressPair_owner (p : Problem) (i : Fin p.incidences) :
    (addressPair p i).1=(owner p i).val := rfl

 theorem addressPairs_eq (p : Problem) :
    List.ofFn (addressPair p)=PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask :=
  List.ofFn_get _

 theorem produced_inventory_le {base : Data} {N B : ℕ}
    (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (R : ℕ) (low : List Bool) (t : Fin p.Q) (H : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : ProducedHeads base p.n N p.incidences (rows p a tail) low
      (FiberRel (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)
        (entryNat (packing p a tail) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R t) H)
      B (t.val*p.r) tables)
    (hlen : tables.length=p.r) (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    (tables.map fun table=>table.buckets.length).prod ≤
      commonBase p.n H ^ labelRows p a tail R low := by
  have htable : ProducedHeads base p.n N p.incidences (rows p a tail) low
      (FiberRel (List.ofFn (addressPair p))
        (entryNat (packing p a tail) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R t) H)
      B (t.val*p.r) tables := by simpa only [addressPairs_eq] using ht
  exact fiber_product_le_maxTotalRank (packing p a tail) (owner p)
    (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R t
    (addressPair p) (addressPair_owner p) H htable hlen hW Finset.univ (Finset.mem_univ t)

 theorem produced_enumeration_le {base : Data} {N B : ℕ}
    (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (R : ℕ) (low : List Bool) (t : Fin p.Q) (H : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : ProducedHeads base p.n N p.incidences (rows p a tail) low
      (FiberRel (PackingIncidenceInput.Semantics.nativeEntries p.scopes p.mask)
        (entryNat (packing p a tail) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R t) H)
      B (t.val*p.r) tables)
    (hlen : tables.length=p.r) (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    (BucketTupleProgram.enumerate tables).length ≤ commonBase p.n H ^ labelRows p a tail R low := by
  rw [BucketTupleProgram.enumerate_length]
  exact produced_inventory_le p a tail R low t H ht hlen hW

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
