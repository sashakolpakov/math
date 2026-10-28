import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramRowCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-! Literal block-lookup and incidence-fiber circuits for the ring source rows.
The branches are exactly those implemented by the packing metadata lookup;
this file identifies their polynomial meanings without any field assumption. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpRowInterpolation SubexponentialSAT.SubexpTaylorExecution
open LayoutPullback

variable {I U C O : Type*} [Fintype I] [DecidableEq I]
  [Fintype U] [DecidableEq U] [CommRing O]

noncomputable def packedValue (P : PackingData I U)
    (rows : U → U → Polynomial O) (v w : I) : Polynomial O :=
  match P.lookup v with
  | none => if w = v then 1 else 0
  | some (j,u) => match P.lookup w with
    | none => 0
    | some (k,y) => if j = k then rows u y else 0

omit [Fintype I] in
theorem packedValue_eq (P : PackingData I U) (rows : U → U → Polynomial O) (v w : I) :
    packedValue P rows v w = LayoutBlocks.assembledRow P.completeBlocks rows v w := by
  cases hv : P.lookup v with
  | none =>
      rw [LayoutBlocks.assembledRow_outside _ _ _ ((P.lookup_none_iff v).mp hv)]
      simp only [packedValue, hv]
      split_ifs <;> simp
  | some z =>
      rcases z with ⟨j,u⟩
      have hv' := (P.lookup_some_iff v (j,u)).mp hv
      rw [← hv', LayoutBlocks.assembledRow_apply]
      cases hw : P.lookup w with
      | none =>
          have hout : w ∉ Set.range (P.completeBlocks.blockEmbedding j) := by
            rintro ⟨a,ha⟩
            exact (P.lookup_none_iff w).mp hw ⟨(j,a),ha⟩
          rw [row_eq_zero _ _ _ hout]
          simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hw]
      | some z =>
          rcases z with ⟨k,y⟩
          have hw' := (P.lookup_some_iff w (k,y)).mp hw
          rw [← hw']
          by_cases hj : j = k
          · subst k
            change packedValue P rows (P.completeBlocks.embed (j,u))
              (P.completeBlocks.embed (j,y)) = _
            rw [show P.completeBlocks.embed (j,y) = P.completeBlocks.blockEmbedding j y from rfl,
              row_apply_injective _ (P.completeBlocks.blockEmbedding j).injective]
            simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at,
              SubexponentialSAT.BlockPacking.CompleteBlocks.blockEmbedding]
          · have hout : P.completeBlocks.embed (k,y) ∉
                Set.range (P.completeBlocks.blockEmbedding j) := by
              rintro ⟨a,ha⟩
              have he := P.completeBlocks.embed.injective ha
              exact hj (congrArg Prod.fst he)
            rw [row_eq_zero _ _ _ hout]
            simp [packedValue, PackingData.completeBlocks_apply, PackingData.lookup_at, hj]

def packedCode (ops : RingProgram C) (P : PackingData I U)
    (localCode : U → U → PolynomialCode C) (v w : I) : PolynomialCode C :=
  match P.lookup v with
  | none => .constant (if w = v then ops.oneRun.1 else ops.zeroRun.1)
  | some (j,u) => match P.lookup w with
    | none => .constant ops.zeroRun.1
    | some (k,y) => if j = k then localCode u y else .constant ops.zeroRun.1

omit [Fintype I] in
theorem packedCode_decode (ops : RepresentedRing C O) (P : PackingData I U)
    (localCode : U → U → PolynomialCode C) (rows : U → U → Polynomial O)
    (hlocal : ∀ u y, (mapCode ops.decode (localCode u y)).denote = rows u y)
    (v w : I) :
    (mapCode ops.decode (packedCode ops.program P localCode v w)).denote =
      LayoutBlocks.assembledRow P.completeBlocks rows v w := by
  rw [← packedValue_eq]
  cases hv : P.lookup v with
  | none =>
      by_cases h : w = v <;> simp [packedCode, packedValue, hv, h, mapCode,
        PolynomialCode.denote, ops.one_correct, ops.zero_correct]
  | some z =>
      rcases z with ⟨j,u⟩
      cases hw : P.lookup w with
      | none => simp [packedCode, packedValue, hv, hw, mapCode,
          PolynomialCode.denote, ops.zero_correct]
      | some z =>
          rcases z with ⟨k,y⟩
          by_cases h : j = k <;> simp [packedCode, packedValue, hv, hw, h, hlocal,
            mapCode, PolynomialCode.denote, ops.zero_correct]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
