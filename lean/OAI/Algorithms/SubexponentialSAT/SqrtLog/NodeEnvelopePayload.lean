import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsProduced
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsFinal

namespace OAI.Algorithms

/-! Direct bounds on retained assignment payloads. Signature keys and their
matrix computation do not occur in the emitted moment bucket records. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT MomentsAssembly BucketTupleProgram LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds

theorem actual_bucket_count (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (b : Table.Bucket)
    (hb : b∈actualBuckets W rows js n h) : b.2.length ≤ 2^h := by
  obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp hb
  exact (SubexponentialSAT.Subexp.PackingBucketTable.selected_length_le _ _).trans
    (by simp [BucketProgram.Controller.labelledRecords,BucketProgram.Label.labelled])

theorem actual_choice_width (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h H C : ℕ) (mask context : List Bool)
    (hjs : ∀ j∈js,j < n) (hm : mask.length=n) (hc : context.length ≤ C) (hh : h ≤ H)
    (v : HeadInput)
    (hv : v∈(HeadTable.mk mask context (actualBuckets W rows js n h)).choices) :
    (Encoding.frame v.bits).length ≤ 4*n+4*C+4*(2^H*(2*n+1))+7 := by
  simp only [HeadTable.choices,List.mem_reverse,List.mem_map] at hv
  obtain ⟨b,hb,rfl⟩ := hv
  have hcount := (actual_bucket_count W rows js n h b hb).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh)
  have hraw : (rawFrames b.2).length=b.2.length*(2*n+1) := by
    rw [Representative.rawFrames_eq_words]
    exact SubexponentialSAT.Subexp.MatrixProgramSupport.words_length b.2 n
      (actualBuckets_width W rows js n h hjs b hb)
  simp only [Encoding.length_frame,HeadInput.bits,List.length_append,hm,hraw]
  nlinarith

theorem produced_choice_width {base : LeafHeadSetupProgram.Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ} {table : HeadTable}
    (hp : ProducedHead base n N D rows low Rel B z table) (W S H : ℕ)
    (hs : preparationSize n N rows low W z ≤ S)
    (hh : (selectedHeads n rows low z).length ≤ H) :
    ∀ v∈table.choices,
      (Encoding.frame v.bits).length ≤ 4*n+20*S^2+4*(2^H*(2*n+1))+7 := by
  obtain ⟨_,hmask,hctx,_⟩ := producedHead_resources hp W 0
  have hctx' : table.context.length ≤ 5*S^2 := hctx.trans (by gcongr)
  obtain ⟨mr,ys,hr,hy,rfl⟩ := hp
  intro v hv
  have hv' := actual_choice_width (base.stacks 141) ys (selectedHeads n rows low z)
    n (selectedHeads n rows low z).length H (5*S^2)
    (selectedMask n rows low z) (selectedContext n N rows z)
    (HeadIdentifierProgram.chosenIds_bound _ _) hmask hctx' hh v hv
  convert hv' using 1 ; ring

theorem produced_choices_width {base : LeafHeadSetupProgram.Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ} {tables : List HeadTable}
    (hp : ProducedHeads base n N D rows low Rel B z tables) (W S H rCap : ℕ)
    (hz : z+tables.length ≤ rCap)
    (hs : ∀ z ≤ rCap,preparationSize n N rows low W z ≤ S)
    (hh : ∀ z < rCap,(selectedHeads n rows low z).length ≤ H) :
    ∀ t∈tables,∀ v∈t.choices,
      (Encoding.frame v.bits).length ≤ 4*n+20*S^2+4*(2^H*(2*n+1))+7 := by
  induction hp with
  | nil => simp
  | @cons z t ts hhead htail ih =>
    have hz' : z ≤ rCap := by simp only [List.length_cons] at hz; omega
    have hzlt : z < rCap := by simp only [List.length_cons] at hz; omega
    have hi := ih (by simp only [List.length_cons] at hz; omega)
    intro t' ht v hv
    rcases List.mem_cons.mp ht with rfl|ht
    · exact produced_choice_width hhead W S H (hs z hz') (hh z hzlt) v hv
    · exact hi t' ht v hv

/-- A complete moment-bucket stream, including every retained assignment,
has a quadratic bound in the bounded tuple stream and ambient width. -/
theorem produced_bucket_stream {base : LeafHeadSetupProgram.Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ} {tables : List HeadTable}
    (hp : ProducedHeads base n N D rows low Rel B z tables) (W S H rCap K : ℕ)
    (hz : z+tables.length ≤ rCap)
    (hs : ∀ z ≤ rCap,preparationSize n N rows low W z ≤ S)
    (hh : ∀ z < rCap,(selectedHeads n rows low z).length ≤ H)
    (hk : (tables.map fun t=>t.buckets.length).prod ≤ K) :
    (bucketsInput (((enumerate tables).map (Representative.bucket n)).reverse)).length ≤
      502*(n+1+(2*(rCap*(4*n+20*S^2+4*(2^H*(2*n+1))+7))+2)*K+1)^2 := by
  have hbytes := enumerate_bytes tables _ (produced_choices_width hp W S H rCap hz hs hh)
  have hlen : tables.length ≤ rCap := by omega
  have hbytes' : (Representative.tuplesBits (enumerate tables)).length ≤
      n+1+(2*(rCap*(4*n+20*S^2+4*(2^H*(2*n+1))+7))+2)*K := by
    calc
      _ ≤ 1+(2*(tables.length*(4*n+20*S^2+4*(2^H*(2*n+1))+7))+2)*
          (tables.map fun t=>t.buckets.length).prod := hbytes
      _ ≤ _ := by gcongr; omega
  have hpayload := final_payload_bound (List.replicate n false) (enumerate tables)
    (n+1+(2*(rCap*(4*n+20*S^2+4*(2^H*(2*n+1))+7))+2)*K)
    (by simp only [List.length_replicate]; omega) hbytes'
    (by simpa using enumerate_valid n tables (producedHeads_valid hp))
  simpa only [List.length_replicate] using hpayload

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms
