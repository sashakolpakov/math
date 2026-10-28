import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryHeads
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputPackingTransport

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open SubexponentialSAT.MulticolorTypes PackingCallerProgram LeafProgram.NodeConcrete
open PackingIncidenceInput BucketProgram

variable (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
  (A R : ℕ) (t : Fin p.Q)

def queryMatrix : ℕ → ℕ → ℤ :=
  LayoutProducedMatrix.literalNat
    (addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail))
    (addressedOwner p) A R t

theorem query_finalized (hmask : p.mask.length=p.n)
    {base : LeafHeadSetupProgram.Data} {B mass : ℕ} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base p.n p.factors
      (addressedEntries p.scopes p.n p.mask).length (ProducedQueryRank.rows p a tail)
      (p.mask.map Bool.not)
      (ProducedRank.FiberRel (addressedEntries p.scopes p.n p.mask)
        (ProducedRank.entryNat (ProducedQueryRank.packing p a tail) A R t) mass)
      B (t.val*p.r) tables)
    (hlen : tables.length=p.r)
    (hW : mass ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    FinalizedMeaning (planHigh p) (queryFreeHead p a tail t)
      (addressedEntries p.scopes p.n p.mask).length
      (queryMatrix p a tail A R t) tables hlen := by
  have he : ProducedRank.entryNat
      (addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)) A R t=
      ProducedRank.entryNat (ProducedQueryRank.packing p a tail) A R t := by
    funext i j
    exact addressedPacking_entryNat p.scopes p.n p.mask _ A R t i j
  apply producedHeads_literal_finalized (base:=base) (N:=p.factors) (B:=B) (z:=t.val*p.r)
    (planHigh p) (queryFreeHead p a tail t)
    (addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail))
    (addressedOwner p) A R t (fun i=>(addressedEntries p.scopes p.n p.mask).get i)
    (addressedOwner_get p) mass ?_ hlen (fun g v=>query_ids_spec p a tail t hmask g v) hW
  simpa only [List.ofFn_get,he] using hp

theorem query_masks (hmask : p.mask.length=p.n)
    {base : LeafHeadSetupProgram.Data} {D B : ℕ}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base p.n p.factors D
      (ProducedQueryRank.rows p a tail) (p.mask.map Bool.not) Rel B (t.val*p.r) tables)
    (hlen : tables.length=p.r) (g : Fin p.r) :
    (tables.get (Fin.cast hlen.symm g)).mask=
      List.ofFn (headMask (planHigh p) (queryFreeHead p a tail t) g) := by
  exact producedHeads_masks hp hlen (fun g v=>query_ids_spec p a tail t hmask g v) g

theorem query_contexts
    {base : LeafHeadSetupProgram.Data} {D B : ℕ}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base p.n p.factors D
      (ProducedQueryRank.rows p a tail) (p.mask.map Bool.not) Rel B (t.val*p.r) tables)
    (hlen : tables.length=p.r) (g : Fin p.r) :
    LeafStatisticsProgram.Arity.decoded (tables.get (Fin.cast hlen.symm g)).context=
      (List.range p.factors).filter (fun f=>decide (planColor p a tail t f=g)) := by
  obtain ⟨mr,ys,hr,hy,ht⟩ := producedHeads_get hp (Fin.cast hlen.symm g)
  rw [ht]
  exact query_context_ids p a tail t g

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
