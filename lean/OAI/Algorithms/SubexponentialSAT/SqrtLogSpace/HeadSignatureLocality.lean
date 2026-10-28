import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBuckets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrixNatural
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingBranch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceConfiguration

/-! Exact full-integer head labels and fixed-high cancellation, extracted
unchanged from HeadSourceLocality. All raw rows and original coordinate IDs
are retained; source-product locality remains in the importing module. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def freeHeadInclusion {n r : ℕ} (H : Finset (Fin n))
    (head : Fin n → Fin r) (g : Fin r) :
    Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g ↪ Moments.Head head g :=
  ⟨fun v => ⟨v.val.val,v.property⟩, by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : Moments.Head head g => v.val) h⟩

/-- Equal fixed-high bits cancel; the remaining exact signature is the full
integer signature on the actual free coordinates of this head. -/
theorem signature_eq_of_free {n r D : ℕ} (H : Finset (Fin n))
    (head : Fin n → Fin r) (g : Fin r) (C : Fin D → Fin n → ℤ)
    (x y : Fin n → Bool) (hhigh : ∀ v ∈ H,x v=y v)
    (hfree : LayoutSignatureBound.boolSignature
        (fun j (v : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g) => C j v.val.val)
        (fun v => x v.val.val) =
      LayoutSignatureBound.boolSignature
        (fun j (v : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g) => C j v.val.val)
        (fun v => y v.val.val)) :
    LayoutSignatureBound.boolSignature (fun j (v : Moments.Head head g) => C j v.val)
      (fun v => x v.val) =
    LayoutSignatureBound.boolSignature (fun j (v : Moments.Head head g) => C j v.val)
      (fun v => y v.val) := by
  classical
  funext j
  let e := freeHeadInclusion H head g
  have he :
      (∑ v : Moments.Head head g, C j v.val *
        ((if x v.val then 1 else 0 : ℤ)-(if y v.val then 1 else 0))) =
      ∑ v : Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g,
        C j v.val.val * ((if x v.val.val then 1 else 0 : ℤ)-
          (if y v.val.val then 1 else 0)) := by
    calc
      _ = ∑ v ∈ Finset.univ.map e, C j v.val *
          ((if x v.val then 1 else 0 : ℤ)-(if y v.val then 1 else 0)) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro v _ hn
        have hH : v.val ∈ H := by
          by_contra hv
          exact hn (Finset.mem_map.mpr ⟨⟨⟨v.val,hv⟩,v.property⟩,Finset.mem_univ _,rfl⟩)
        simp [hhigh v.val hH]
      _ = _ := by rw [Finset.sum_map]; rfl
  simp only [mul_sub,Finset.sum_sub_distrib] at he
  have hf := congrFun hfree j
  simp only [LayoutSignatureBound.boolSignature,LayoutExactBuckets.signature] at hf ⊢
  apply sub_eq_zero.mp
  rw [he,hf,sub_self]


open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram

variable {r Q d n : ℕ}

/-- Actual full integer keys use every emitted raw row, restricted only to
this head's free original coordinates. -/
def freeLabel (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (a : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    Fin ps.length → ℤ :=
  LayoutSignatureBound.boolSignature
    (fun j v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val v.val.val.val) a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
