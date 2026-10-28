import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBootResources

namespace OAI.Algorithms

/-! A uniform ordinary polynomial envelope for the actually executed cache
and address initialization. Parameters are charged by their runtime lengths. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem cacheBound_polynomial (height R width : List Bool) (S : ℕ)
    (hh : height.length ≤ S) (hr : R.length ≤ S) (hw : width.length ≤ S) :
    cacheBound height R width ≤ 10000*(S+1)^4 := by
  have hb : cacheBound height R width ≤
      7*(S+S+S)+(12*S+400*(S+1)*(S+1)*(2*S*S+5)+
        110*(S+1)*(S+(1+2*S*S)+4)+16)+11*S+27 := by
    unfold cacheBound LayoutProgram.IntegerCache.flatCost
    gcongr
  calc
    _ ≤ _ := hb
    _ ≤ _ := by nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4)]

theorem cacheWords_flat_length (words : List (List Bool)) (W : ℕ)
    (hw : ∀ word∈words,word.length=W) : words.flatten.length=words.length*W := by
  induction words with
  | nil => simp
  | cons word words ih =>
      rw [List.flatten_cons,List.length_append,ih (by intro w h; exact hw w (by simp [h]))]
      rw [hw word (by simp)]
      simp [Nat.add_mul,Nat.add_comm]

theorem initializeCost_polynomial (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (r t : ℕ) (records : List (List Bool)) (height R width : List Bool)
    (words : List (List Bool)) (S : ℕ)
    (ha : WordBound S a) (hr : r ≤ S) (ht : t ≤ S)
    (hb : (SubexponentialSAT.Encoding.encodeList id records).length ≤ S)
    (hh : height.length ≤ S) (hR : R.length ≤ S) (hw : width.length ≤ S)
    (hlen : words.length=R.length) (hwords : ∀ word∈words,word.length=width.length) :
    initializeCost a ra rd rc r t records height R width words ≤ 20000*(S+1)^4 ∧
      WordBound (2*(S+1)^2+3) (nodeStart a ra rd rc r t records height R width words) := by
  let K := (S+1)^2
  have hSK : S ≤ K := by dsimp [K]; nlinarith
  have hSK' : S+1 ≤ K := by dsimp [K]; nlinarith
  have hprod : S*S ≤ K := by dsimp [K]; nlinarith
  have hrt : t*r ≤ K := (Nat.mul_le_mul ht hr).trans hprod
  have hn : records.length ≤ K := (Nat.le_trans
    (Nat.le_of_succ_le (SubexponentialSAT.Encoding.length_encodeList_lower id records)) hb).trans hSK
  have hflat : words.flatten.length ≤ K := by
    rw [cacheWords_flat_length words width.length hwords,hlen]
    exact (Nat.mul_le_mul hR hw).trans hprod
  have hneg : R.length*width.length ≤ K := (Nat.mul_le_mul hR hw).trans hprod
  have hden : (LayoutProgram.IntegerCache.denominatorWord R.length).length ≤ K := by
    simp only [LayoutProgram.IntegerCache.denominatorWord,List.length_append,List.length_replicate,
      List.length_singleton]
    omega
  have he := initializeCost_staging a ra rd rc r t records height R width words K
    (boot_wordBound_mono ha hSK)
    (addressResult_wordBound ra r t K (hr.trans hSK) (ht.trans hSK) hrt)
    (rowCountState_wordBound rd records K (hb.trans hSK) hn)
    (cacheState_wordBound rc height R width words K (hh.trans hSK) (hR.trans hSK)
      (hw.trans hSK) hflat hneg hden)
  refine ⟨?_,he.2⟩
  have had := Address.budget_polynomial r t
  have ha2 : 40*(r+t+1)^2 ≤ 40*(S+S+1)^2 := by gcongr
  have hc := cacheBound_polynomial height R width S hh hR hw
  have hd := rowCountBudget_linear records
  have hcost := he.1
  dsimp [K] at hcost
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
