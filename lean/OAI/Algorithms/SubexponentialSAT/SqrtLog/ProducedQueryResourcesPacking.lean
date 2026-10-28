import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesConstructor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankProvenance
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads

namespace OAI.Algorithms

/-! The resource geometry is read from the actual searched packing and its
emitted original-variable word rows. No rank or head-size number is supplied
as a machine input. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open LeafQueryFrontend
noncomputable section

abbrev problem (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k)) :=
  LeafProgram.Query.packingProblem q k hg

/-- Exactly the forward low mask consumed by the head identifier program. -/
def lowBytes (q : Query) : List Bool := q.forward.map Bool.not

def rank (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : ℕ :=
  let p := problem q k hg
  let R := (LeafParametersProgram.produce (q.input k)).R
  CostAssembly.maxTotalRank Finset.univ
    (BucketProgram.ProducedRank.actualRank (ProducedQueryRank.packing p a tail)
      (ProducedQueryRank.owner p) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R
      (ProducedQueryRank.rows p a tail) (lowBytes q))

def headSize (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : ℕ :=
  let p := problem q k hg
  LayoutProducedHeads.maxSelected p.n p.Q p.r (ProducedQueryRank.rows p a tail) (lowBytes q)

def ofPacking (q : Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : CostAssembly.Resources :=
  make q k B (rank q k hg a tail) (headSize q k hg a tail) C d qi e

theorem selected_length_le (q : Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (t : Fin (problem q k hg).Q) (g : Fin (problem q k hg).r) :
    (LeafHeadSetupProgram.selectedHeads (problem q k hg).n
      (ProducedQueryRank.rows (problem q k hg) a tail) (lowBytes q)
      (t.val*(problem q k hg).r+g.val)).length ≤ (ofPacking q k B C d qi e hg a tail).headSize :=
  LayoutProducedHeads.selected_le_max _ _ _ _ _ t g

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
