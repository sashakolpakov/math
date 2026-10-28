import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramTuples
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPayload

namespace OAI.Algorithms

/-! Paid storage bounds for the actual Cartesian append. The whole attained
bucket table, rather than a selected representative, is included in M. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram

 theorem nextRows_bytes_le (rows : List (List Bool)) (mask context : List Bool)
    (bs : List Table.Bucket) (M : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ M) (hn : rows.length ≤ M)
    (hm : mask.length ≤ M) (hc : context.length ≤ M) (hb : (Table.tableBits bs).length ≤ M) :
    (SubexponentialSAT.ProgramEncoding.encodeRecords (Expand.nextRows rows mask context bs)).length ≤ 50*(M+1)^3 := by
  have hcount : bs.length ≤ M := by
    have h := SubexponentialSAT.Encoding.length_encodeList_lower Table.payload bs
    change bs.length+1 ≤ (Table.tableBits bs).length at h
    omega
  have hal : ∀ w ∈ Expand.alphabet mask context bs, w.length ≤ 12*M+7 := by
    intro w hw
    have h := alphabet_word_width mask context bs w hw
    omega
  have hw := ProductBounds.output_width rows (Expand.alphabet mask context bs) M (12*M+7) hr hal
  have he := SubexponentialSAT.Encoding.length_encodeList_upper id (Expand.nextRows rows mask context bs)
    (M+(12*M+7)) hw
  rw [Expand.nextRows_length] at he
  have he0 : (SubexponentialSAT.ProgramEncoding.encodeRecords (Expand.nextRows rows mask context bs)).length ≤
      1+(26*M+16)*(rows.length*bs.length) := by
    convert he using 1 ; ring
  have he' : (SubexponentialSAT.ProgramEncoding.encodeRecords (Expand.nextRows rows mask context bs)).length ≤
      1+(26*M+16)*(M*M) := he0.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul hn hcount)) 1)
  nlinarith only [he',Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3)]

 theorem tuple_local_bound (regs : Fin 10 → Bool) (rows : List (List Bool)) (mask context : List Bool)
    (bs : List Table.Bucket) (M : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ M) (hn : rows.length ≤ M)
    (hm : mask.length ≤ M) (hc : context.length ≤ M) (hb : (Table.tableBits bs).length ≤ M) :
    WordBound (50*(M+1)^3) (Expand.state regs (Expand.nextRows rows mask context bs) mask context [] []) := by
  have hout := nextRows_bytes_le rows mask context bs M hr hn hm hc hb
  have hsmall : M ≤ 50*(M+1)^3 := by nlinarith only [Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have hone : 1 ≤ 50*(M+1)^3 := by
    have hx : 0 < 50*(M+1)^3 := by positivity
    omega
  intro i
  fin_cases i <;> simp only [Expand.state,Matrix.cons_val_succ',Matrix.cons_val_zero',
    List.length_nil,List.length_cons] <;> first | exact hout | omega

 theorem tuple_stage_bound (a : Data) (regs : Fin 10 → Bool) (rows : List (List Bool))
    (mask context : List Bool) (bs : List Table.Bucket) (M : ℕ)
    (ha : WordBound M a) (hr : ∀ row ∈ rows, row.length ≤ M) (hn : rows.length ≤ M)
    (hm : mask.length ≤ M) (hc : context.length ≤ M) (hb : (Table.tableBits bs).length ≤ M) :
    WordBound (50*(M+1)^3) (tupleResult a regs rows mask context bs) ∧
    tupleCost a regs rows mask context bs ≤ 3000000*(M+1)^4 := by
  let C := 50*(M+1)^3
  have hsmall : M ≤ C := by dsimp [C]; nlinarith only [Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have ha' := wordBound_mono ha hsmall
  have ho := tuple_local_bound regs rows mask context bs M hr hn hm hc hb
  constructor
  · exact returned_wordBound tupleRegs (by decide) tupleInputs tupleOutputs a _ C
      tupleInputs_protected tupleOutputs_protected (by decide) (by decide) ha' ho
  · have hs := stageCost_linear tupleRegs (by decide) tupleInputs tupleOutputs a _
      (Expand.cost rows mask context bs+1) C tupleInputs_protected tupleOutputs_protected
      (by decide) (by decide) ha' ho
    change tupleCost a regs rows mask context bs ≤ _ at hs
    norm_num [tupleInputs,tupleOutputs] at hs
    have he := expansion_cost_polynomial rows mask context bs (2*M)
      (fun row hx => (hr row hx).trans (by omega)) (hn.trans (by omega)) (by omega) (hb.trans (by omega))
    have hp : (2*M+1)^4 ≤ 16*(M+1)^4 := by
      calc
        _ ≤ (2*(M+1))^4 := by gcongr ; omega
        _ = _ := by ring
    have hp34 : (M+1)^3 ≤ (M+1)^4 := pow_le_pow_right₀ (by omega) (by decide)
    have hp1 : 1 ≤ (M+1)^4 := one_le_pow₀ (by omega)
    dsimp [C] at hs
    nlinarith only [hs,he,hp,hp34,hp1]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
