import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrixRank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramDispatch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPaddedSpan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankUniversal

namespace OAI.Algorithms

/-! The actual integer entry program is a literal owner-fiber sum. Restricting
its columns to the emitted head IDs has exactly the canonical pulled row span,
up to harmless column omission/repetition. All incidence rows are retained. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutProgram

variable {r Q : ℕ} {I V O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [CommRing O]
variable {node : Fin Q → O}

def literalMatrix (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (A R : ℕ) (t : Fin Q) : I → V → ℤ :=
  fun j => row owner (localEntry P A R t j)

def headOwner (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i)) (t : Fin Q) (g : Fin r) :
    IncidenceHead P t g → {v : V // head t v=g} :=
  LayoutHeadPullback.headOwner owner (fun i=>(P.label i).head t) (head t)
    (fun i=>hhead i t) g

omit [Fintype V] in
theorem literalMatrix_head (P : PackingData I (UniversalType r Q 1))
    (owner : I → V) (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (j : I) (v : {v : V // head t v=g}) :
    literalMatrix P owner A R t j v.val =
      pulledConstraints (headOwner P owner head hhead t g)
        (paddedConstraint P A R t g) j v := by
  rw [literalMatrix,LayoutHeadPullback.row_restrict owner
    (fun i=>(P.label i).head t) (head t) (fun i=>hhead i t) g]
  apply congrArg (fun f => row (headOwner P owner head hhead t g) f v)
  funext w
  exact localEntry_eq P A R t g j w.val w.property

theorem literalHead_rank (P : PackingData I (UniversalType r Q 1))
    (owner : I → V) (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    LayoutRank.rowRank (fun j (v : {v : V // head t v=g}) =>
      literalMatrix P owner A R t j v.val) =
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  have he : (fun j (v : {v : V // head t v=g}) =>literalMatrix P owner A R t j v.val) =
      pulledConstraints (headOwner P owner head hhead t g) (paddedConstraint P A R t g) := by
    funext j v
    exact literalMatrix_head P owner head hhead A R t g j v
  rw [he]
  obtain ⟨h1,h2⟩ := paddedConstraint_pullback_spans P A R denom hdenom units t g
    (headOwner P owner head hhead t g)
  exact LayoutRank.rowRank_eq_of_mutual_span _ _ h2 h1

theorem selected_literal_rank_le {K : Type*} [Fintype K]
    (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (selected : K → {v : V // head t v=g}) :
    LayoutRank.rowRank (fun j k=>literalMatrix P owner A R t j (selected k).val) ≤
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  have h := LayoutRank.rowRank_columns_le
    (fun j (v : {v : V // head t v=g})=>literalMatrix P owner A R t j v.val) selected
  rw [literalHead_rank P owner head hhead A R denom hdenom units t g] at h
  exact h

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
