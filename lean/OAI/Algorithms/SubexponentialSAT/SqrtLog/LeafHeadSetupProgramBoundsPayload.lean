import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramProductBounds

namespace OAI.Algorithms

/-! Actual bucket-product payload sizes. Every bucket retains its full list
of assignments; no representative-only size estimate is used here. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open BucketTupleProgram
open BucketTupleProgram.Representative (headsBits tuplesBits)
open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput)

 theorem encoded_member_length {A : Type*} (enc : A → List Bool) (xs : List A)
    (x : A) (hx : x ∈ xs) : (enc x).length ≤ (SubexponentialSAT.Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [SubexponentialSAT.Encoding.length_encodeList_cons]
        omega
      · have h := ih hx
        simp only [SubexponentialSAT.Encoding.length_encodeList_cons]
        omega

 theorem bucket_words_le (bs : List Table.Bucket) (b : Table.Bucket) (hb : b ∈ bs) :
    (SubexponentialSAT.Subexp.MatrixProgramSupport.words b.2).length ≤ (Table.tableBits bs).length := by
  have h := encoded_member_length Table.payload bs b hb
  simp only [Table.payload, List.length_append, SubexponentialSAT.Encoding.length_frame] at h
  exact (Nat.le_add_left _ _).trans h

 theorem alphabet_word_width (mask context : List Bool) (bs : List Table.Bucket)
    (word : List Bool) (hw : word ∈ Expand.alphabet mask context bs) :
    word.length ≤ 4*mask.length+4*context.length+4*(Table.tableBits bs).length+7 := by
  simp only [Expand.alphabet, List.mem_reverse, List.mem_map] at hw
  obtain ⟨b,hb,rfl⟩ := hw
  have h := bucket_words_le bs b hb
  simp only [Table.alphabetWord, Table.headBits, List.length_append, SubexponentialSAT.Encoding.length_frame]
  omega

 theorem choices_word_width (table : HeadTable) (h : HeadInput) (hh : h ∈ table.choices) :
    (SubexponentialSAT.Encoding.frame h.bits).length ≤
      4*table.mask.length+4*table.context.length+4*(Table.tableBits table.buckets).length+7 := by
  apply alphabet_word_width table.mask table.context table.buckets
  rw [alphabet_eq]
  exact List.mem_map.mpr ⟨h,hh,rfl⟩

 theorem extend_width (rows : List (List HeadInput)) (choices : List HeadInput) (R L : ℕ)
    (hr : ∀ row ∈ rows, (headsBits row).length ≤ R)
    (hc : ∀ h ∈ choices, (SubexponentialSAT.Encoding.frame h.bits).length ≤ L) :
    ∀ row ∈ extend rows choices, (headsBits row).length ≤ R+L := by
  intro row hrow
  have hm : headsBits row ∈ (extend rows choices).map headsBits := List.mem_map.mpr ⟨row,hrow,rfl⟩
  rw [extend_bits] at hm
  apply ProductBounds.output_width _ _ R L _ _ (headsBits row) hm
  · intro w hw; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw; exact hr x hx
  · intro w hw; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw; exact hc x hx

 theorem enumerateFrom_width (tables : List HeadTable) (rows : List (List HeadInput)) (R L : ℕ)
    (hr : ∀ row ∈ rows, (headsBits row).length ≤ R)
    (ht : ∀ table ∈ tables, ∀ h ∈ table.choices, (SubexponentialSAT.Encoding.frame h.bits).length ≤ L) :
    ∀ row ∈ enumerateFrom tables rows, (headsBits row).length ≤ R+tables.length*L := by
  induction tables generalizing rows R with
  | nil => simpa [enumerateFrom] using hr
  | cons table tables ih =>
      have he := extend_width rows table.choices R L hr (ht table (by simp))
      have hi := ih (extend rows table.choices) (R+L) he
        (fun t hm => ht t (by simp [hm]))
      simpa only [enumerateFrom,List.length_cons,Nat.add_mul,Nat.one_mul,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hi

 theorem enumerateFrom_bytes (tables : List HeadTable) (rows : List (List HeadInput)) (R L : ℕ)
    (hr : ∀ row ∈ rows, (headsBits row).length ≤ R)
    (ht : ∀ table ∈ tables, ∀ h ∈ table.choices, (SubexponentialSAT.Encoding.frame h.bits).length ≤ L) :
    (tuplesBits (enumerateFrom tables rows)).length ≤
      1+(2*(R+tables.length*L)+2)*(rows.length*(tables.map fun h=>h.buckets.length).prod) := by
  have h := SubexponentialSAT.Encoding.length_encodeList_upper headsBits (enumerateFrom tables rows)
    (R+tables.length*L) (enumerateFrom_width tables rows R L hr ht)
  simpa only [tuplesBits,enumerateFrom_length] using h

 theorem enumerate_bytes (tables : List HeadTable) (L : ℕ)
    (ht : ∀ table ∈ tables, ∀ h ∈ table.choices, (SubexponentialSAT.Encoding.frame h.bits).length ≤ L) :
    (tuplesBits (enumerate tables)).length ≤
      1+(2*(tables.length*L)+2)*(tables.map fun h=>h.buckets.length).prod := by
  simpa [enumerate] using enumerateFrom_bytes tables [[]] 0 L (by simp [headsBits]) ht

 theorem bucketProduct_positive (tables : List HeadTable)
    (hne : ∀ table ∈ tables, 1 ≤ table.buckets.length) :
    1 ≤ (tables.map fun h => h.buckets.length).prod := by
  induction tables with
  | nil => simp
  | cons t ts ih =>
      have ht := hne t (by simp)
      have hs := ih (fun u hu => hne u (by simp [hu]))
      simp only [List.map_cons, List.prod_cons]
      nlinarith only [ht,hs]

 theorem prefix_product_le (tables : List HeadTable) (j : ℕ)
    (hne : ∀ table ∈ tables, 1 ≤ table.buckets.length) :
    ((tables.take j).map fun h=>h.buckets.length).prod ≤
      (tables.map fun h=>h.buckets.length).prod := by
  induction tables generalizing j with
  | nil => simp
  | cons table tables ih =>
      have hh := hne table (by simp)
      have ht : ∀ t ∈ tables, 1 ≤ t.buckets.length := fun t hm => hne t (by simp [hm])
      cases j with
      | zero =>
          have hp : 1 ≤ (tables.map fun h=>h.buckets.length).prod := by
            exact bucketProduct_positive tables ht
          simp only [List.take_zero,List.map_nil,List.prod_nil,List.map_cons,List.prod_cons]
          nlinarith only [hh,hp]
      | succ j =>
          simpa only [List.take_succ_cons,List.map_cons,List.prod_cons] using
            Nat.mul_le_mul_left table.buckets.length (ih j ht)

 theorem expansion_cost_polynomial (rows : List (List Bool)) (mask context : List Bool)
    (bs : List Table.Bucket) (Z : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ Z) (hn : rows.length ≤ Z)
    (hm : mask.length+context.length ≤ Z) (hb : (Table.tableBits bs).length ≤ Z) :
    Expand.cost rows mask context bs ≤ 100000*(Z+1)^4 := by
  have hcount : bs.length ≤ Z := by
    have h := SubexponentialSAT.Encoding.length_encodeList_lower Table.payload bs
    change bs.length+1 ≤ (Table.tableBits bs).length at h
    omega
  have hal : ∀ w ∈ Expand.alphabet mask context bs, w.length ≤ 8*Z+7 := by
    intro w hw
    have h := alphabet_word_width mask context bs w hw
    omega
  have hlen : (Expand.alphabet mask context bs).length = bs.length := by simp [Expand.alphabet]
  have hstep := ProductBounds.stepCost_le rows (Expand.alphabet mask context bs) Z (8*Z+7) hr hal
  rw [hlen] at hstep
  have hbytes := SubexponentialSAT.Encoding.length_encodeList_upper id (Expand.alphabet mask context bs) (8*Z+7) hal
  rw [hlen] at hbytes
  have htable := Table.cost_le mask context bs
  have hstep' : SubexponentialSAT.Subexp.TupleProgram.stepCost rows (Expand.alphabet mask context bs) ≤
      150*(rows.length+1)*(bs.length+1)*(9*Z+8) := by
    convert hstep using 1 ; ring
  have hs : SubexponentialSAT.Subexp.TupleProgram.stepCost rows (Expand.alphabet mask context bs) ≤
      150*(Z+1)*(Z+1)*(9*Z+8) := hstep'.trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1)) (Nat.add_le_add_right hcount 1)))
  have ht : Table.cost mask context bs ≤ 300*(Z+1)^2 := by
    calc
      _ ≤ 300*(Z+1)*(Z+1) := htable.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 300 (Nat.add_le_add_right hm 1)) (Nat.add_le_add_right hb 1))
      _ = _ := by ring
  have hbytes' : (SubexponentialSAT.ProgramEncoding.encodeRecords (Expand.alphabet mask context bs)).length ≤
      1+(16*Z+16)*bs.length := by
    convert hbytes using 1 ; ring
  have he : (SubexponentialSAT.ProgramEncoding.encodeRecords (Expand.alphabet mask context bs)).length ≤
      1+(16*Z+16)*Z := hbytes'.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hcount) 1)
  unfold Expand.cost
  nlinarith only [hs,ht,he,Nat.zero_le Z,Nat.zero_le (Z^2),Nat.zero_le (Z^3),Nat.zero_le (Z^4)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end OAI.Algorithms
