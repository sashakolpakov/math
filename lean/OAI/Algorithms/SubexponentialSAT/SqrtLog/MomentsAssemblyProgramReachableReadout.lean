import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableBuckets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRegisterFrame

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

section Native
variable (produce : Code) (p t : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
  (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
  (vars : Finset (Fin n)) (u J : ℕ)
  (relation : AssignmentContext → List Bool → Contribution n (baseWidth p t) d → Prop)
  (validFrame : (Fin 768 → List Bool) → Prop) (H A : ℕ)
  (contract : AssignmentContract p t M cache table u J relation produce degree width vars validFrame A)
include hz hd hw contract


theorem denseCommand_eval (one seed : Raw p t (n:=n) (d:=d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y S K : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : ∀ b ∈ bs, BucketSize H X Y b) (hcount : ss.length ≤ S) (hbcount : bs.length ≤ K)
    (hbytes : (base 169).length ≤ H)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (baseWidth p t) d vars u J validFrame base ss bs)
    (zero : RingProgram.Code (Word (baseWidth p t)) d) (shape : List Bool) (hshape : shape.length=n)
    (h102 : base 102 = []) (h190 : base 190 = RingProgram.flat zero) (h191 : base 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, base i = []) :
    let e := Product.environment p t M cache table degree width u J
    ∃ entries, BucketsRel p t M cache table u J relation ss one bs seed entries ∧
      EntryInvariant vars u J entries ∧
      ∃ k ≤ denseBudget (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S K A,
      ∃ rr, Eval (denseCommand produce) k
        (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
        (machine rr (emptyCore e) (Function.update (bucketStream base (Product.bytes entries) []) 102
          (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J))) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  obtain ⟨entries,hr,hi,na,ha,r1,h1⟩ := command_eval produce p t M cache hz table degree width hd hw
    vars u J relation validFrame H A contract one seed ss bs base regs X Y S K ho hsi hsize hcount hbcount
    hbytes hsupports hone hclean h162 h170 h177 hv
  let high := bucketStream base (Product.bytes entries) []
  obtain ⟨nr,hb,r2,h2⟩ := readout_machine_eval p t M cache table entries zero degree width shape
    u J (n+u+J) r1 high hd hw hshape (entryInvariant_keyBound vars u J entries hi)
    (by simp [high,bucketStream,h102]) (by simp [high,bucketStream])
    (by simp [high,bucketStream,h190]) (by simp [high,bucketStream,h191]) (by
      intro i hi
      have hn163 : i ≠ 163 := by intro h; subst i; norm_num [readoutWorkPorts,Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by intro h; subst i; norm_num [readoutWorkPorts,Fin.ext_iff] at hi
      simpa [high,bucketStream,hn163,hn166] using hwork i hi)
  have hbound := readoutBudget_mono (baseWidth p t) d n u J (n+u+J) entries.length
    (dictionaryCapacity vars u J) (entryInvariant_sizes vars u J entries hi).1
  refine ⟨entries,hr,hi,na+nr,?_,r2,h1.seq h2⟩
  dsimp [denseBudget]
  omega

theorem denseCommand_eval_framed (one seed : Raw p t (n:=n) (d:=d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y S K : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : ∀ b ∈ bs, BucketSize H X Y b) (hcount : ss.length ≤ S) (hbcount : bs.length ≤ K)
    (hbytes : (base 169).length ≤ H)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (baseWidth p t) d vars u J validFrame base ss bs)
    (zero : RingProgram.Code (Word (baseWidth p t)) d) (shape : List Bool) (hshape : shape.length=n)
    (h102 : base 102 = []) (h190 : base 190 = RingProgram.flat zero) (h191 : base 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, base i = [])
    (hproducer : ∀ i : Fin 40, 16 ≤ i.val → RegisterFrame.Preserves produce i) :
    let e := Product.environment p t M cache table degree width u J
    ∃ entries, BucketsRel p t M cache table u J relation ss one bs seed entries ∧
      EntryInvariant vars u J entries ∧
      ∃ k ≤ denseBudget (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S K A,
      ∃ rr, Eval (denseCommand produce) k
        (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
        (machine rr (emptyCore e) (Function.update (bucketStream base (Product.bytes entries) []) 102
          (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J))) ∧
        ∀ i : Fin 40, 16 ≤ i.val → rr i=regs i := by
  obtain ⟨entries,hr,hi,k,hk,rr,he⟩ := denseCommand_eval produce p t M cache hz table degree width hd hw
    vars u J relation validFrame H A contract one seed ss bs base regs X Y S K ho hsi hsize hcount hbcount
    hbytes hsupports hone hclean h162 h170 h177 hv zero shape hshape h102 h190 h191 hwork
  exact ⟨entries,hr,hi,k,hk,rr,he,RegisterFrame.dense_eval hproducer he⟩

theorem denseProgram_run (one seed : Raw p t (n:=n) (d:=d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y S K : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : ∀ b ∈ bs, BucketSize H X Y b) (hcount : ss.length ≤ S) (hbcount : bs.length ≤ K)
    (hbytes : (base 169).length ≤ H)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (baseWidth p t) d vars u J validFrame base ss bs)
    (zero : RingProgram.Code (Word (baseWidth p t)) d) (shape : List Bool) (hshape : shape.length=n)
    (h102 : base 102 = []) (h190 : base 190 = RingProgram.flat zero) (h191 : base 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, base i = [])
    (hproducer : ∀ i : Fin 40, 16 ≤ i.val → RegisterFrame.Preserves produce i) :
    let e := Product.environment p t M cache table degree width u J
    ∃ entries, BucketsRel p t M cache table u J relation ss one bs seed entries ∧
      EntryInvariant vars u J entries ∧ ∃ rr,
      RunsIn (denseProgram produce)
        (denseBudget (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S K A+1)
        ((machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs))).withPC
          (some (denseProgram produce).entry))
        ((machine rr (emptyCore e) (Function.update (bucketStream base (Product.bytes entries) []) 102
          (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J))).withPC none) ∧
        ∀ i : Fin 40, 16 ≤ i.val → rr i=regs i := by
  obtain ⟨entries,hr,hi,k,hk,rr,he,hf⟩ := denseCommand_eval_framed produce p t M cache hz table degree width hd hw
    vars u J relation validFrame H A contract one seed ss bs base regs X Y S K ho hsi hsize hcount hbcount
    hbytes hsupports hone hclean h162 h170 h177 hv zero shape hshape h102 h190 h191 hwork hproducer
  exact ⟨entries,hr,hi,rr,⟨k+1,Nat.add_le_add_right hk 1,compiled_halt_trace he 163 102⟩,hf⟩
end Native
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable

end OAI.Algorithms
