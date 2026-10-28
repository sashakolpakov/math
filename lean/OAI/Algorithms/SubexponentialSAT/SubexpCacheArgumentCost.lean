import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentLoops
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentLoopProof

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpCacheArgument

open scoped BigOperators

def payloadBits (cs : List Bits) : ℕ := (cs.map List.length).sum
def allPayloadBits (columns : List (List Bits)) : ℕ := (columns.map payloadBits).sum
def entryCount (columns : List (List Bits)) : ℕ := (columns.map List.length).sum

theorem encode_length (cs : List Bits) :
    (Encoding.encodeList id cs).length = 2*payloadBits cs+2*cs.length+1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Encoding.length_encodeList_cons,id_eq,ih,payloadBits,List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem cache_length (columns : List (List Bits)) :
    (Encoding.encodeList id (columnRecords columns)).length =
      4*allPayloadBits columns+4*entryCount columns+4*columns.length+1 := by
  induction columns with
  | nil => rfl
  | cons cs columns ih =>
    simp only [columnRecords,List.map_cons,Encoding.length_encodeList_cons,id_eq,encode_length,
      allPayloadBits,entryCount,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem rawServiceCost_le (left right j B : ℕ) (mark u : Bool) (c : Bits) :
    SubexpRawArgumentService.cost left right j B mark u c ≤
      37*c.length+26*(left+right+j)+25*B+194 := by
  have hr := SubexpArgumentKeyEmitter.rawCost_le left right j mark u
  have hl := SubexpArgumentEmitLoop.rawKey_length_le left right j mark u
  have hd : B-(SubexpArgumentKeyEmitter.rawKey left right j mark u).length ≤ B := Nat.sub_le _ _
  simp only [SubexpRawArgumentService.cost,SubexpArgumentKeyEmitter.paddedKey,
    List.length_append,List.length_replicate]
  omega

theorem variableCost_le (i right j B : ℕ) (mark u : Bool) (c : Bits) :
    variableCost i right j B mark u c ≤ 40*c.length+33*(i+right+j)+32*B+218 := by
  have h := rawServiceCost_le i right j B mark u c
  unfold variableCost
  omega

theorem innerCost_le (cs : List Bits) (i right j B : ℕ) (u : Bool) :
    innerCost i right j B u cs ≤ 46*payloadBits cs+
      cs.length*(33*(i+right+j+cs.length)+32*B+227)+1 := by
  induction cs generalizing j u with
  | nil => simp [innerCost,payloadBits]
  | cons c cs ih =>
    have hv := variableCost_le i right j B true u c
    have ht := ih (j+1) false
    simp only [innerCost,payloadBits,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem entryCount_le (columns : List (List Bits)) (N : ℕ) (h : ∀ cs∈columns,cs.length ≤ N) :
    entryCount columns ≤ columns.length*N := by
  induction columns with
  | nil => simp [entryCount]
  | cons cs columns ih =>
    have hc := h cs (by simp)
    have ht := ih (fun ds hd => h ds (by simp [hd]))
    simp only [entryCount,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem outerCost_le (columns : List (List Bits)) (i B N : ℕ)
    (h : ∀ cs∈columns,cs.length ≤ N) :
    outerCost i B columns ≤ 64*allPayloadBits columns+
      columns.length*N*(33*(i+columns.length+N)+32*B+247)+27*columns.length+1 := by
  induction columns generalizing i with
  | nil => simp [outerCost,allPayloadBits]
  | cons cs columns ih =>
    have hn := h cs (by simp)
    have ht := ih (i+1) (fun ds hd => h ds (by simp [hd]))
    have hc := innerCost_le cs i columns.length 0 B true
    have hmul : cs.length*(33*(i+columns.length+cs.length)+32*B+247) ≤
        N*(33*(i+(columns.length+1)+N)+32*B+247) := by
      apply Nat.mul_le_mul hn
      omega
    simp only [outerCost,encode_length,allPayloadBits,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem constantCost_le (negative u : Bool) (I : Inputs) :
    constantCost negative u I ≤ 44*(constantWord negative I).length+33*I.dimension+32*I.keyWidth+212 := by
  have h := rawServiceCost_le I.dimension 0 0 I.keyWidth false u (constantWord negative I)
  unfold constantCost
  omega

theorem totalCost_le (beta negative : Bits) (columns : List (List Bits)) (B N : ℕ)
    (h : ∀ cs∈columns,cs.length ≤ N) :
    totalCost beta negative columns B+1 ≤
      44*(beta.length+negative.length)+92*allPayloadBits columns+
      columns.length*N*(33*(columns.length+N)+32*B+275)+130*columns.length+64*B+449 := by
  have hb := constantCost_le false false (cacheInputs beta negative columns B)
  have hn := constantCost_le true true (cacheInputs beta negative columns B)
  have hc := outerCost_le columns 0 B N h
  have he := entryCount_le columns N h
  simp only [constantWord,Bool.false_eq_true,↓reduceIte,cacheInputs] at hb hn
  simp only [totalCost,cacheInputs,cache_length]
  nlinarith

theorem payloadBits_le (cs : List Bits) (W : ℕ) (h : ∀ c∈cs,c.length ≤ W) :
    payloadBits cs ≤ cs.length*W := by
  induction cs with
  | nil => simp [payloadBits]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [payloadBits,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem allPayloadBits_le (columns : List (List Bits)) (N W : ℕ)
    (hN : ∀ cs∈columns,cs.length ≤ N) (hW : ∀ cs∈columns,∀ c∈cs,c.length ≤ W) :
    allPayloadBits columns ≤ columns.length*N*W := by
  induction columns with
  | nil => simp [allPayloadBits]
  | cons cs columns ih =>
    have hc := payloadBits_le cs W (hW cs (by simp))
    have hn := hN cs (by simp)
    have ht := ih (fun ds hd => hN ds (by simp [hd])) (fun ds hd => hW ds (by simp [hd]))
    have hm := Nat.mul_le_mul_right W hn
    simp only [allPayloadBits,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem totalCost_uniform (beta negative : Bits) (columns : List (List Bits)) (B N W : ℕ)
    (hN : ∀ cs∈columns,cs.length ≤ N) (hW : ∀ cs∈columns,∀ c∈cs,c.length ≤ W)
    (hb : beta.length ≤ W) (hn : negative.length ≤ W) :
    totalCost beta negative columns B+1 ≤ (88+92*columns.length*N)*W+
      columns.length*N*(33*(columns.length+N)+32*B+275)+130*columns.length+64*B+449 := by
  have ht := totalCost_le beta negative columns B N hN
  have hp := allPayloadBits_le columns N W hN hW
  nlinarith

end SubexponentialSAT.SubexpCacheArgument

end OAI.Algorithms
