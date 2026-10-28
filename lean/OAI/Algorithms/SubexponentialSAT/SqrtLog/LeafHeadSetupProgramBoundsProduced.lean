import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsEnvelope

namespace OAI.Algorithms

/-! Discharge the per-table size and nonemptiness premises from the actual
controller-produced heads. Empty heads retain their one empty assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram
open BucketTupleProgram.Representative (headsBits tuplesBits)

 theorem producedHead_resources {base : Data} {n N D : ℕ} {rows : List (List Bool)}
    {low : List Bool} {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {table : HeadTable} (hp : ProducedHead base n N D rows low Rel B z table) (W T : ℕ) :
    1 ≤ table.buckets.length ∧ table.mask.length=n ∧
    table.context.length ≤ 5*(preparationSize n N rows low W z)^2 ∧
    (Table.tableBits table.buckets).length ≤
      matrixEnvelope (base.stacks 141) T B D n (selectedHeads n rows low z).length := by
  obtain ⟨mr,ys,hr,hy,rfl⟩ := hp
  exact ⟨actualBuckets_length_pos _ _ _ _ _,selected_mask_length _ _ _ _,
    selected_context_length _ _ _ _ _ _,
    actual_bucket_bytes_le _ _ _ _ _ _ _ _ Rel hr hy (HeadIdentifierProgram.chosenIds_bound _ _)⟩

 theorem producedHeads_payloads {base : Data} {n N D : ℕ} {rows : List (List Bool)}
    {low : List Bool} {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {tables : List HeadTable} (hp : ProducedHeads base n N D rows low Rel B z tables)
    (W T r S E : ℕ) (hz : z+tables.length ≤ r)
    (hS : ∀ u ≤ r,preparationSize n N rows low W u ≤ S)
    (hE : ∀ u ≤ r,matrixEnvelope (base.stacks 141) T B D n (selectedHeads n rows low u).length ≤ E) :
    (∀ table∈tables,1 ≤ table.buckets.length) ∧
    (∀ table∈tables,∀ h∈table.choices,
      (SubexponentialSAT.Encoding.frame h.bits).length ≤ 4*n+20*S^2+4*E+7) := by
  induction hp with
  | nil => simp
  | @cons z table tables hh ht ih =>
      have hz' : z ≤ r := by simp only [List.length_cons] at hz; omega
      obtain ⟨hne,hmask,hc,hb⟩ := producedHead_resources hh W T
      have hcontext : table.context.length ≤ 5*S^2 := hc.trans (by gcongr; exact hS z hz')
      have htable : (Table.tableBits table.buckets).length ≤ E := hb.trans (hE z hz')
      obtain ⟨hne',hwidth'⟩ := ih (by simp only [List.length_cons] at hz; omega)
      constructor
      · intro t hm; rcases List.mem_cons.mp hm with rfl|hm
        · exact hne
        · exact hne' t hm
      · intro t hm h hh'
        rcases List.mem_cons.mp hm with rfl|hm
        · have hw := choices_word_width t h hh'
          rw [hmask] at hw
          omega
        · exact hwidth' t hm h hh'

 theorem initial_costTrace_bound (entry : SubexponentialSAT.StructuredCalls.Cmd 16 256) (base : Data)
    (n N D W : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B A Z r S E K : ℕ)
    {z0 : ℕ} {tables : List HeadTable} {costs : List ℕ} {a f : Data}
    (trace : CostTrace entry base n N D W rows low Rel T B z0 [[]] tables costs a f)
    (produced : ProducedHeads base n N D rows low Rel B z0 tables)
    (ha : WordBound A a) (hsize : n ≤ rows.length) (hrA : r ≤ A)
    (hr : z0+tables.length ≤ r) (hK : (tables.map fun h=>h.buckets.length).prod ≤ K)
    (hbytes : 1+(2*(r*(4*n+20*S^2+4*E+7))+2)*K ≤ A)
    (hQZ : r*(4*n+20*S^2+4*E+7) ≤ Z) (hKZ : K ≤ Z) (hD : D ≤ Z)
    (hprep : A+5*S^2 ≤ Z) (hSZ : S ≤ Z) (hEZ : E ≤ Z)
    (hS : ∀ u ≤ r,preparationSize n N rows low W u ≤ S)
    (hE : ∀ u ≤ r,matrixEnvelope (base.stacks 141) T B D n (selectedHeads n rows low u).length ≤ E) :
    costs.sum ≤ tables.length*(100000000*(Z+1)^4) ∧ WordBound A f := by
  obtain ⟨hne,hw⟩ := producedHeads_payloads produced W T r S E hr hS hE
  apply costTrace_bound entry base n N D W rows low Rel T B A Z r
    (r*(4*n+20*S^2+4*E+7)) K (4*n+20*S^2+4*E+7) hsize hrA hbytes hQZ hKZ hD
    (fun u hu => (by gcongr; exact hS u hu : A+5*(preparationSize n N rows low W u)^2 ≤ A+5*S^2).trans hprep)
    (fun u hu => (hS u hu).trans hSZ) (fun u hu => (hE u hu).trans hEZ) trace 0 ha
    hr hne hw
  · simpa using hK
  · simp [headsBits]
  · simpa only [Nat.zero_add] using
      Nat.mul_le_mul_right (4*n+20*S^2+4*E+7) (show tables.length ≤ r by omega)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end

end OAI.Algorithms
