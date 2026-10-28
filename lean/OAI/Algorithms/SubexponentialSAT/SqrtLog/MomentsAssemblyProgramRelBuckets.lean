import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelSupports

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
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


theorem bucketStep_eval (one seed : Raw p t (n:=n) (d:=d)) (ss : List (Finset (Fin n)))
    (b : BucketInput) (tail : List Bool) (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y S : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : BucketSize H X Y b) (hcount : ss.length ≤ S) (hbytes : (high 169).length ≤ H)
    (hsrc : high 163 = Encoding.frame b.bits ++ tail)
    (hsupports : high 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : high 167 = Product.bytes one) (hseed : high 166 = Product.bytes seed)
    (hclean : SupportClean high) (h162 : high 162 = []) (h170 : high 170 = []) (h177 : high 177 = [])
    (hv : SupportFrames (n:=n) validFrame (bucketHigh high b tail) b.heads) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, BucketStep p t M cache table u J relation ss one seed b out ∧ EntryInvariant vars u J out ∧
      ∃ k ≤ bucketEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S A,
      ∃ rr, Eval (bucketStep produce) k (machine regs (emptyCore e) high)
        (machine rr (emptyCore e) (bucketFinished high tail (Product.bytes out))) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let base := bucketHigh high b tail
  obtain ⟨r1,h1⟩ := startBucket_eval regs (emptyCore e) high b tail hsrc
    (hclean 164 (Or.inl (by decide))) (hclean 176 (Or.inl (by decide))) h177 h170 h162
    (hclean 179 (Or.inl (by decide)))
  have hc : SupportClean base := by
    intro i hi
    have h163 : i ≠ 163 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    have h162' : i ≠ 162 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    have h170' : i ≠ 170 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    have h177' : i ≠ 177 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    by_cases h176 : i = 176
    · subst i; simp [base,bucketHigh,bucketHigh3]
    · simpa [base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,h163,h162',h170',h177',h176]
        using hclean i hi
  obtain ⟨out,hr,hoi,ns,hs,r2,h2⟩ := supportScan_eval produce p t M cache hz table degree width hd hw
    vars u J relation validFrame H A contract one seed ss b.heads base r1 X Y ho hsi
    hsize.2.2.2.2 hsize.2.2.2.1
    (by simpa [base,bucketHigh,bucketHigh3] using hsize.2.2.1)
    (by simp [base,bucketHigh,bucketHigh3])
    (by simpa [base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using hone) hc hv
  have hb : supportStream base (Product.bytes seed) (rawFrames (ss.map Squarefree.encodeMask)) = base := by
    funext i
    by_cases hi : i = 166
    · subst i; simp [supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,hseed]
    by_cases hj : i = 162
    · subst i; simp [supportStream,base,bucketHigh,hsupports]
    simp [supportStream,hi,hj]
  rw [hb] at h2
  let afterSupports := supportStream base (Product.bytes out) []
  obtain ⟨r3,h3⟩ := finishBucket_eval r2 (emptyCore e) afterSupports
  have hout : Function.update (Function.update afterSupports 177 []) 170 [] =
      bucketFinished high tail (Product.bytes out) := by
    funext i
    by_cases ha : i = 166
    · subst i; simp [afterSupports,supportStream,bucketFinished]
    by_cases hb : i = 170
    · subst i; simp [bucketFinished,h170]
    by_cases hc : i = 177
    · subst i; simp [bucketFinished,h177]
    by_cases hd : i = 162
    · subst i; simp [afterSupports,supportStream,bucketFinished,h162]
    by_cases he : i = 176
    · subst i
      simp [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketFinished,
        hclean 176 (Or.inl (by decide))]
    by_cases hf : i = 163
    · subst i; simp [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,bucketFinished]
    simp [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,bucketFinished,ha,hb,hc,hd,he,hf]
  have h3' : Eval finishBucket (2*b.context.length+3+(2*(rawFrames (b.heads.map HeadInput.bits)).length+3))
      (machine r2 (emptyCore e) afterSupports)
      (machine r3 (emptyCore e) (bucketFinished high tail (Product.bytes out))) := by
    rw [hout] at h3
    simpa [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using h3
  have hct := Nat.mul_le_mul_right
    (supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A+2) hcount
  refine ⟨out,?_,hoi,bucketHeaderBudget high b+(ns+
    (2*b.context.length+3+(2*(rawFrames (b.heads.map HeadInput.bits)).length+3))),?_,r3,?_⟩
  · simpa [BucketStep,base,bucketHigh,bucketHigh3,bucketHigh2] using hr
  · rcases hsize with ⟨hb,hc,hh,hcount',hhs⟩
    dsimp [bucketEnvelope,bucketHeaderBudget]
    omega
  · simpa only [bucketStep,afterSupports] using h1.seq (h2.seq h3')

theorem command_eval (one seed : Raw p t (n:=n) (d:=d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y S K : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : ∀ b ∈ bs, BucketSize H X Y b) (hcount : ss.length ≤ S) (hbcount : bs.length ≤ K)
    (hbytes : (base 169).length ≤ H)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (n:=n) validFrame base bs) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, BucketsRel p t M cache table u J relation ss one bs seed out ∧ EntryInvariant vars u J out ∧
      ∃ k ≤ K*(bucketEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S A+2)+2,
      ∃ rr, Eval (command produce) k
        (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
        (machine rr (emptyCore e) (bucketStream base (Product.bytes out) [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let inv := fun (a : Raw p t (n:=n) (d:=d)) (tapes : Fin 768 → List Bool) =>
    EntryInvariant vars u J a ∧ ∃ source, tapes =
      (machine (fun _ => false) (emptyCore e) (bucketStream base (Product.bytes a) source)).stacks
  have body : BodyContract 163 (bucketStep produce) BucketInput.bits
      (BucketStep p t M cache table u J relation ss one)
      (bucketEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S A)
      inv (fun b => b ∈ bs) := by
    intro a b tail state hmem hi hsrc
    obtain ⟨hai,source,htapes⟩ := hi
    have hsource : source = Encoding.frame b.bits ++ tail := by
      have he := (congrFun htapes 163).symm.trans hsrc
      simpa [machine,bucketStream] using he
    subst source
    let high := bucketStream base (Product.bytes a) (Encoding.frame b.bits ++ tail)
    have heq : state = machine state.regs (emptyCore e) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    have hc : SupportClean high := by
      intro i hi
      have hn163 : i ≠ 163 := by intro he; subst i; norm_num [Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by intro he; subst i; norm_num [Fin.ext_iff] at hi
      simpa [high,bucketStream,hn163,hn166] using hclean i hi
    obtain ⟨out,hr,hoi,k,hk,rr,he⟩ := bucketStep_eval produce p t M cache hz table degree width hd hw
      vars u J relation validFrame H A contract one a ss b tail high state.regs X Y S ho hai
      (hsize b hmem) hcount (by simpa [high,bucketStream] using hbytes)
      (by simp [high,bucketStream]) (by simpa [high,bucketStream] using hsupports)
      (by simpa [high,bucketStream] using hone) (by simp [high,bucketStream]) hc
      (by simp [high,bucketStream,h162]) (by simp [high,bucketStream,h170])
      (by simp [high,bucketStream,h177]) (hv b hmem (Product.bytes a) _ tail)
    let result := machine rr (emptyCore e) (bucketStream base (Product.bytes out) tail)
    refine ⟨out,hr,k,hk,result,⟨hoi,tail,rfl⟩,?_,?_⟩
    · simp [result,machine,bucketStream]
    · rw [heq]
      simpa only [high,bucketFinished_stream,result] using he
  obtain ⟨out,hr,k,hk,state,hi,hsrc,he⟩ := rawScan_eval 163 (bucketStep produce) BucketInput.bits
    (BucketStep p t M cache table u J relation ss one)
    (bucketEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S A)
    inv (fun b => b ∈ bs) body bs seed
    (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
    (fun _ h => h) ⟨hsi,_,rfl⟩ (by simp [machine,bucketStream,streamBits,bucketsInput])
  obtain ⟨hoi,source,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 163).symm.trans hsrc
    simpa [machine,bucketStream] using hh
  have heq : state = machine state.regs (emptyCore e) (bucketStream base (Product.bytes out) []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · simpa [machine, hsource] using htapes
  refine ⟨out,hr,hoi,k,?_,state.regs,?_⟩
  · exact hk.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hbcount) 2)
  · rw [heq] at he
    exact he
end Native
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
