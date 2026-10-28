import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramHeadFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsStep

namespace OAI.Algorithms

/-! Resource induction over the actual head trace. The remaining bucket
product is part of the invariant; no bound is obtained by iterating the
polynomial callback estimate. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.UnaryForPrograms
open BucketTupleProgram
open BucketTupleProgram.Representative (headsBits tuplesBits)

 theorem popped_wordBound (a : Data) (A : ℕ) (ha : WordBound A a) :
    WordBound A (popped headPorts a) := by
  intro i
  by_cases hi : i=headPorts.counter
  · subst i
    rw [popped_counter]
    simp only [List.length_tail]
    have h := ha headPorts.counter
    change (a.stacks 648).length ≤ A at h
    omega
  · rw [popped_other _ _ _ hi]
    exact ha i

 theorem bucketProduct_one_le (tables : List HeadTable)
    (hne : ∀ table∈tables,1 ≤ table.buckets.length) :
    1 ≤ (tables.map fun h=>h.buckets.length).prod := by
  induction tables with
  | nil => simp
  | cons t ts ih =>
      have hh := hne t (by simp)
      have ht := ih (fun u hu => hne u (by simp [hu]))
      simp only [List.map_cons,List.prod_cons]
      nlinarith only [hh,ht]

 theorem costTrace_bound (entry : Cmd 16 256) (base : Data) (n N D W : ℕ)
    (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (A Z r Q K L : ℕ) (hsize : n ≤ rows.length) (hrA : r ≤ A)
    (hbytes : 1+(2*Q+2)*K ≤ A) (hQZ : Q ≤ Z) (hKZ : K ≤ Z) (hD : D ≤ Z)
    (hprep : ∀ u ≤ r,A+5*(preparationSize n N rows low W u)^2 ≤ Z)
    (hS : ∀ u ≤ r,preparationSize n N rows low W u ≤ Z)
    (hE : ∀ u ≤ r,matrixEnvelope (base.stacks 141) T B D n (selectedHeads n rows low u).length ≤ Z)
    {z : ℕ} {prior : Representative.Tuples} {tables : List HeadTable} {costs : List ℕ}
    {a f : Data} (trace : CostTrace entry base n N D W rows low Rel T B z prior tables costs a f) :
    ∀ R : ℕ, WordBound A a → z+tables.length ≤ r →
      (∀ table∈tables,1 ≤ table.buckets.length) →
      (∀ table∈tables,∀ h∈table.choices,(SubexponentialSAT.Encoding.frame h.bits).length ≤ L) →
      prior.length*(tables.map fun h=>h.buckets.length).prod ≤ K →
      (∀ row∈prior,(headsBits row).length ≤ R) → R+tables.length*L ≤ Q →
      costs.sum ≤ tables.length*(100000000*(Z+1)^4) ∧ WordBound A f := by
  induction trace with
  | nil z prior a hcounter =>
      intro R ha hz hne ht hcount hw hwidth
      exact ⟨by simp,popped_wordBound a A ha⟩
  | @cons z prior table tables cost costs a e f hcounter record hecounter tail ih =>
      intro R ha hz hne ht hcount hw hwidth
      have hz' : z ≤ r := by simp only [List.length_cons] at hz; omega
      have hb := popped_wordBound a A ha
      obtain ⟨hf,ha649,ha660,rp,mb,rt,mr,ys,hmr,hys,htable,heval,hmrun,heq,hcost⟩ := record
      have h141 : (popped headPorts a).stacks 141=base.stacks 141 := hf 141 (by decide) (by simp [loopMutable])
      have hys' : List.Forall₂
          (List.Forall₂ (BucketProgram.shiftedWord ((popped headPorts a).stacks 141))) mr ys := by
        simpa only [h141] using hys
      have hremaining : 1 ≤ ((table::tables).map fun h=>h.buckets.length).prod :=
        bucketProduct_one_le _ hne
      have hprior : prior.length ≤ K := by nlinarith only [hcount,hremaining]
      have hR : R ≤ Q := by omega
      have hstep := headStep_cost_le entry (popped headPorts a) rp mb rt n N D W z T B A Z
        rows (prior.map headsBits) low mr ys Rel hmr hys' hmrun hb hsize
        (hprep z hz') (hS z hz') hD (by simpa only [h141] using hE z hz')
        (by intro row hrow; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hrow; exact (hw x hx).trans (hR.trans hQZ))
        (by simpa only [List.length_map] using hprior.trans hKZ)
      have hc : cost ≤ 100000000*(Z+1)^4 := hcost.trans hstep
      have hne' : ∀ t∈tables,1 ≤ t.buckets.length := fun t hm => hne t (by simp [hm])
      have ht' : ∀ t∈tables,∀ h∈t.choices,(SubexponentialSAT.Encoding.frame h.bits).length ≤ L :=
        fun t hm => ht t (by simp [hm])
      have hprod' : 1 ≤ (tables.map fun h=>h.buckets.length).prod := bucketProduct_one_le _ hne'
      have hcount' : (extend prior table.choices).length*(tables.map fun h=>h.buckets.length).prod ≤ K := by
        simpa only [extend_length,choices_length,List.map_cons,List.prod_cons,Nat.mul_assoc] using hcount
      have hnextCount : (extend prior table.choices).length ≤ K := by nlinarith only [hcount',hprod']
      have hnextWidth := extend_width prior table.choices R L hw (ht table (by simp))
      have hwidth' : R+L+tables.length*L ≤ Q := by simpa only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hwidth
      have hnextQ : ∀ row∈extend prior table.choices,(headsBits row).length ≤ Q :=
        fun row hm => (hnextWidth row hm).trans (by omega)
      have hencoded := SubexponentialSAT.Encoding.length_encodeList_upper headsBits (extend prior table.choices) Q hnextQ
      have hencoded' : (tuplesBits (extend prior table.choices)).length ≤ A :=
        (hencoded.trans (show 1+(2*Q+2)*(extend prior table.choices).length ≤ 1+(2*Q+2)*K by gcongr)).trans hbytes
      have hphysical : (SubexponentialSAT.ProgramEncoding.encodeRecords
          (Expand.nextRows (prior.map headsBits) (selectedMask n rows low z) (selectedContext n N rows z)
            (actualBuckets ((popped headPorts a).stacks 141) ys (selectedHeads n rows low z)
              n (selectedHeads n rows low z).length))).length ≤ A := by
        rw [h141]
        rw [tuplesBits_eq,←nextRows_eq] at hencoded'
        simpa only [htable] using hencoded'
      have hea : WordBound A e := by
        rw [heq]
        exact headStepResult_wordBound (popped headPorts a) rp mb rt n N W z A rows
          (prior.map headsBits) low ys hb (by simp only [List.length_cons] at hz; omega) ha649 hphysical
      obtain ⟨htail,hfa⟩ := ih (R+L) hea (by simp only [List.length_cons] at hz; omega)
        hne' ht' hcount' hnextWidth hwidth'
      refine ⟨?_,hfa⟩
      simp only [List.sum_cons,List.length_cons]
      nlinarith only [hc,htail]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
