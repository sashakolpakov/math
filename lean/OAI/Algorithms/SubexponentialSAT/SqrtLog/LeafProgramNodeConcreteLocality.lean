import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteRows
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrixNatural

namespace OAI.Algorithms

/-! Equality of the integer signatures emitted by the actual matrix implies
exact equality of the source-row baseline in the full coefficient ring. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutExactBuckets LayoutPullback

variable {r Q d D n : ℕ}

abbrev pulled (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i)) :=
  LayoutHeadPullback.pullback owner id head (copied p P) (fun t i=>hhead i t)

theorem literal_signature_eq (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (t : Fin Q) (g : Fin r) (x y : {v : Fin n //head t v=g} → ℤ)
    (hxy : signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
      p.aWord.length p.R t j.val v.val.val) x =
      signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
      p.aWord.length p.R t j.val v.val.val) y) :
    (pulled p P owner head hhead).bucketLabel t g x =
      (pulled p P owner head hhead).bucketLabel t g y := by
  have he : (fun (j : Fin D) (v : {v : Fin n //head t v=g}) =>
      LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t j.val v.val.val) =
      pulledConstraints (LayoutProducedMatrix.headOwner P owner head hhead t g)
        (paddedConstraint P p.aWord.length p.R t g) := by
    funext j v
    rw [LayoutProducedMatrix.literalNat_fin]
    exact LayoutProducedMatrix.literalMatrix_head P owner head hhead _ _ t g j v
  rw [he] at hxy
  have hs := (paddedConstraint_pullback_spans P p.aWord.length p.R p.denom p.hdenom
    (p.model.nodeUnits p.t Q p.ht p.hfield) t g
    (LayoutProducedMatrix.headOwner P owner head hhead t g)).1
  have hr : signature (pulledConstraints (LayoutProducedMatrix.headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (universal p) P.completeBlocks t g)) x =
      signature (pulledConstraints (LayoutProducedMatrix.headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (universal p) P.completeBlocks t g)) y := by
    funext j
    apply sub_eq_zero.mp
    rw [← signature_sub]
    apply integer_kernel_of_rational_span _ _ hs (x-y) _ j
    intro k
    rw [signature_sub,congrFun hxy k,sub_self]
  funext j
  exact congrFun hr ((Fintype.equivFin (LayoutBlocks.RowIndex (universal p) P.completeBlocks t g)).symm j)

theorem pulled_baseline_eq (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (t : Fin Q) (i : Fin D) (x y : Fin n → ℤ)
    (hown : ∀ v,head t v=(P.label i).slot 0 t → x v=y v)
    (hother : ∀ g,g≠(P.label i).slot 0 t →
      signature (fun (j : Fin D) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t j.val v.val.val)
        (fun v=>x v.val) =
      signature (fun (j : Fin D) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t j.val v.val.val)
        (fun v=>y v.val)) :
    (∑ v,(row owner (packedValue P p.rows i) v).eval (p.model.node p.t Q p.ht p.hfield t)*(x v : p.model.O p.t)) =
    ∑ v,(row owner (packedValue P p.rows i) v).eval (p.model.node p.t Q p.ht p.hfield t)*(y v : p.model.O p.t) := by
  have he : packedValue P p.rows i = LayoutBlocks.assembledRow P.completeBlocks p.rows i := by
    funext v
    exact packedValue_eq P p.rows i v
  rw [he]
  apply (pulled p P owner head hhead).nodeValue_eq_of_buckets t i x y
  · funext v
    exact hown v.val v.property
  · intro g hg
    exact literal_signature_eq p P owner head hhead t g _ _ (hother g hg)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
