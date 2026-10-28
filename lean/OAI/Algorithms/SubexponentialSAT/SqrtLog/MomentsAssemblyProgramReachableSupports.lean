import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableHeads

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

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


theorem supportStep_eval (one seed : Raw p t (n:=n) (d:=d)) (s : Finset (Fin n))
    (hs : List HeadInput) (tail : List Bool) (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : ∀ h ∈ hs, HeadSize H X h) (hcount : hs.length ≤ Y) (hbytes : (high 170).length ≤ H)
    (hsrc : high 162 = Encoding.frame (Squarefree.encodeMask s) ++ tail)
    (hheads : high 170 = rawFrames (hs.map HeadInput.bits))
    (hone : high 167 = Product.bytes one) (hseed : high 166 = Product.bytes seed)
    (h160 : high 160 = []) (h161 : high 161 = []) (h164 : high 164 = []) (h168 : high 168 = [])
    (h174 : high 174 = []) (h175 : high 175 = []) (h176 : high 176 = []) (h178 : high 178 = [])
    (h179 : high 179 = [])
    (hwork : ∀ i : Fin 768, 180 ≤ i.val → i.val ≤ 188 → high i = [])
    (hv : HeadFrames validFrame (supportHigh high (Squarefree.encodeMask s) tail) hs) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, SupportStep p t M cache table u J relation (high 177) hs one seed s out ∧
      EntryInvariant vars u J out ∧
      ∃ k ≤ supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A,
      ∃ rr, Eval (supportStep produce) k (machine regs (emptyCore e) high)
        (machine rr (emptyCore e) (supportFinished high tail (Product.bytes out))) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let base := supportHigh high (Squarefree.encodeMask s) tail
  obtain ⟨r1,h1⟩ := startSupport_eval one e regs high (Squarefree.encodeMask s) tail
    hsrc h164 h168 h179 h161 hone
  obtain ⟨product,hr,hpi,nh,hh,r2,h2⟩ := headScan_eval produce p t M cache hz table degree width hd hw
    vars u J relation validFrame H A contract base
    (by simp [base,supportHigh,h164]) (by simp [base,supportHigh,h176])
    (by simp [base,supportHigh,h178]) (by simp [base,supportHigh,h175])
    (by simp [base,supportHigh,h160]) (by simp [base,supportHigh,h174]) hs X hsize hv one r1 ho
  have hbase : Function.update base 161 (rawFrames (hs.map HeadInput.bits)) = base := by
    funext i
    by_cases hi : i = 161
    · subst i; simp [base,supportHigh,hheads]
    · simp [hi]
  rw [hbase] at h2
  let afterHeads := Function.update base 161 []
  obtain ⟨nf,hf,r3,h3⟩ := finishSupport_eval p t M cache table degree width hd hw u J s
    product seed afterHeads r2
    (by simp [afterHeads,base,supportHigh]) (by simp [afterHeads,base,supportHigh,hseed])
    (by simp [afterHeads,base,supportHigh,h164]) (by simp [afterHeads,base,supportHigh,h179]) (by
      intro i hi hj
      have h1 : i ≠ 161 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      have h2 : i ≠ 168 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      have h3 : i ≠ 162 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      simpa [afterHeads,base,supportHigh,h1,h2,h3] using hwork i hi hj)
  let out := supportValue p t M cache s product seed
  have hout : supportOutput afterHeads (Product.bytes out) = supportFinished high tail (Product.bytes out) := by
    funext i
    by_cases ha : i = 166
    · subst i; simp [supportOutput,supportFinished]
    by_cases hb : i = 168
    · subst i; simp [supportOutput,supportFinished,h168]
    by_cases hc : i = 161
    · subst i; simp [supportOutput,supportFinished,afterHeads,h161]
    by_cases he : i = 162
    · subst i; simp [supportOutput,supportFinished,afterHeads,base,supportHigh]
    simp [supportOutput,supportFinished,afterHeads,base,supportHigh,ha,hb,hc,he]
  have hoi : EntryInvariant vars u J out :=
    ⟨supportValue_valid p t M cache vars u J s product seed hpi.1 hsi.1,
      supportValue_nodup p t M cache s product seed hsi.2⟩
  have hb := finishSupportBudget_le p t M cache vars u J s product seed hpi hsi
  have hob := (entryInvariant_sizes vars u J one ho).2
  have hct := Nat.mul_le_mul_right
    (headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A+2) hcount
  refine ⟨out,⟨product,?_,rfl⟩,hoi,
    (9*n+7+7*(Product.bytes one).length+5+7*(high 170).length+5)+(nh+nf),?_,r3,?_⟩
  · simpa [base,supportHigh] using hr
  · dsimp [supportEnvelope]; omega
  · rw [hout] at h3
    simpa only [supportStep,Squarefree.encodeMask,List.length_ofFn,base,afterHeads,out]
      using h1.seq (h2.seq h3)

theorem supportScan_eval (one seed : Raw p t (n:=n) (d:=d)) (ss : List (Finset (Fin n)))
    (hs : List HeadInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (X Y : ℕ) (ho : EntryInvariant vars u J one) (hsi : EntryInvariant vars u J seed)
    (hsize : ∀ h ∈ hs, HeadSize H X h) (hcount : hs.length ≤ Y)
    (hbytes : (base 170).length ≤ H)
    (hheads : base 170 = rawFrames (hs.map HeadInput.bits)) (hone : base 167 = Product.bytes one)
    (hclean : SupportClean base) (hv : SupportFrames (baseWidth p t) d vars u J validFrame base ss hs) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, SupportsRel p t M cache table u J relation (base 177) hs one ss seed out ∧
      EntryInvariant vars u J out ∧
      ∃ k ≤ ss.length*(supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A+2)+2,
      ∃ rr, Eval (supportScan produce) k
        (machine regs (emptyCore e) (supportStream base (Product.bytes seed) (rawFrames (ss.map Squarefree.encodeMask))))
        (machine rr (emptyCore e) (supportStream base (Product.bytes out) [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let inv := fun (a : Raw p t (n:=n) (d:=d)) (tapes : Fin 768 → List Bool) =>
    EntryInvariant vars u J a ∧ ∃ source, source.length ≤ (rawFrames (ss.map Squarefree.encodeMask)).length ∧ tapes =
      (machine (fun _ => false) (emptyCore e) (supportStream base (Product.bytes a) source)).stacks
  have body : BodyContract 162 (supportStep produce) Squarefree.encodeMask
      (SupportStep p t M cache table u J relation (base 177) hs one)
      (supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A)
      inv (fun s => s ∈ ss) := by
    intro a s tail state hmem hi hsrc
    obtain ⟨hai,source,hlen,htapes⟩ := hi
    have hsource : source = Encoding.frame (Squarefree.encodeMask s) ++ tail := by
      have he := (congrFun htapes 162).symm.trans hsrc
      simpa [machine,supportStream] using he
    subst source
    have htail : tail.length ≤ (rawFrames (ss.map Squarefree.encodeMask)).length := by
      simp only [List.length_append] at hlen
      omega
    let high := supportStream base (Product.bytes a) (Encoding.frame (Squarefree.encodeMask s) ++ tail)
    have heq : state = machine state.regs (emptyCore e) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    have hc : SupportClean high := by
      intro i hi
      have hn162 : i ≠ 162 := by intro he; subst i; norm_num [Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by intro he; subst i; norm_num [Fin.ext_iff] at hi
      simpa [high,supportStream,hn162,hn166] using hclean i hi
    obtain ⟨b,hr,hbi,k,hk,rr,he⟩ := supportStep_eval produce p t M cache hz table degree width hd hw
      vars u J relation validFrame H A contract one a s hs tail high state.regs X Y ho hai
      hsize hcount (by simpa [high,supportStream] using hbytes)
      (by simp [high,supportStream]) (by simpa [high,supportStream] using hheads)
      (by simpa [high,supportStream] using hone) (by simp [high,supportStream])
      (hc 160 (Or.inl (by decide))) (hc 161 (Or.inl (by decide)))
      (hc 164 (Or.inl (by decide))) (hc 168 (Or.inl (by decide)))
      (hc 174 (Or.inl (by decide))) (hc 175 (Or.inl (by decide)))
      (hc 176 (Or.inl (by decide))) (hc 178 (Or.inl (by decide)))
      (hc 179 (Or.inl (by decide))) (fun i hi hj => hc i (Or.inr ⟨hi,hj⟩))
      (hv a hai _ hlen s hmem tail htail)
    let out := machine rr (emptyCore e) (supportStream base (Product.bytes b) tail)
    refine ⟨b,?_,k,hk,out,⟨hbi,tail,htail,rfl⟩,?_,?_⟩
    · simpa [high,supportStream] using hr
    · simp [out,machine,supportStream]
    · rw [heq]
      simpa only [high,supportFinished_stream,out] using he
  obtain ⟨out,hr,k,hk,state,hi,hsrc,he⟩ := rawScan_eval 162 (supportStep produce) Squarefree.encodeMask
    (SupportStep p t M cache table u J relation (base 177) hs one)
    (supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A)
    inv (fun s => s ∈ ss) body ss seed
    (machine regs (emptyCore e) (supportStream base (Product.bytes seed) (rawFrames (ss.map Squarefree.encodeMask))))
    (fun _ h => h) ⟨hsi,_,le_rfl,rfl⟩ (by simp [machine,supportStream,streamBits])
  obtain ⟨hoi,source,hlen,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 162).symm.trans hsrc
    simpa [machine,supportStream] using hh
  have heq : state = machine state.regs (emptyCore e) (supportStream base (Product.bytes out) []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [htapes,hsource]
      rfl
  refine ⟨out,hr,hoi,k,hk,state.regs,?_⟩
  rw [heq] at he
  exact he
end Native
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable

end OAI.Algorithms
