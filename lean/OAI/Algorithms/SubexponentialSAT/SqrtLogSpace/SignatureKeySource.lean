import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSignatureLocality
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadOrder

/-!
# Actual full signature keys and the source head labels

The selected-coordinate list retains its physical order. The equivalence below
is the existing explicit selected-ID equivalence; it neither sorts assignments
nor replaces the full raw matrix by a basis.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open BucketTupleProgram.Concrete
open LayoutProgram


variable {r Q d n : ℕ}

/-- Reindexing the actual selected columns gives exactly the full integer
label used by source locality, with every original row retained. -/
theorem ordered_signature (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ _ : v ∉ H, head node v = g)
    (a : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    LayoutSignatureBound.boolSignature
      (fun (j : Fin ps.length) (i : Fin js.length) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i))
      (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs a) =
      HeadSourceLocality.freeLabel p ps P owner head H node g a := by
  funext j
  exact (freeOrder H (fun v => head node v.val) g js hb hn hs).sum_comp
    (fun v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node
      j.val v.val.val.val * (if a v then 1 else 0 : ℤ))

/-- Exact byte equality of keys computed from the ordered shifted matrix is
equivalent to equality of the full source labels. The coefficient premise is
the pointwise interpretation proved for the actual native loader output. -/
theorem key_eq_freeLabel (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ _ : v ∉ H, head node v = g)
    (W : List Bool) (c : Fin ps.length → Fin js.length → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i))
    (x y : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    BucketProgram.signatureValue W
        (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs x))
        (List.ofFn (fun j => List.ofFn (c j))) =
      BucketProgram.signatureValue W
        (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs y))
        (List.ofFn (fun j => List.ofFn (c j))) ↔
      HeadSourceLocality.freeLabel p ps P owner head H node g x =
        HeadSourceLocality.freeLabel p ps P owner head H node g y := by
  rw [AttainedSignatureProgram.key_eq_iff W c _ _ _ hc]
  rw [ordered_signature p ps P owner head H node g js hb hn hs x,
    ordered_signature p ps P owner head H node g js hb hn hs y]

/-- The actual binary cursor has the same full-key equality as the source
assignment obtained from the explicit selected-coordinate equivalence. -/
theorem naturalKey_eq_freeLabel (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ _ : v ∉ H, head node v = g)
    (W : List Bool) (c : Fin ps.length → Fin js.length → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i))
    (x y : Fin (2 ^ js.length)) :
    AttainedSignatureProgram.Rescan.naturalKey W (List.ofFn (fun j => List.ofFn (c j)))
        js.length x.val =
      AttainedSignatureProgram.Rescan.naturalKey W (List.ofFn (fun j => List.ofFn (c j)))
        js.length y.val ↔
      HeadSourceLocality.freeLabel p ps P owner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs).symm
          (AttainedSignatures.assignmentEquiv js.length x)) =
      HeadSourceLocality.freeLabel p ps P owner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs).symm
          (AttainedSignatures.assignmentEquiv js.length y)) := by
  simpa only [AttainedSignatureProgram.Rescan.naturalKey, Equiv.apply_symm_apply,
    AttainedSignatures.assignment_word] using
    key_eq_freeLabel p ps P owner head H node g js hb hn hs W c hc
      ((freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs).symm
        (AttainedSignatures.assignmentEquiv js.length x))
      ((freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs).symm
        (AttainedSignatures.assignmentEquiv js.length y))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
