import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableNative

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


theorem headStep_eval (left : Raw p t (n:=n) (d:=d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool) (h : HeadInput) (tail : List Bool)
    (X : ℕ) (hl : EntryInvariant vars u J left) (hsize : HeadSize H X h)
    (hsource : high 161 = Encoding.frame h.bits ++ tail)
    (h164 : high 164 = []) (h176 : high 176 = []) (h178 : high 178 = [])
    (h175 : high 175 = []) (h160 : high 160 = []) (h174 : high 174 = [])
    (hv : AssignmentFrames validFrame (headHigh high h tail) h.assignments) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, HeadStep p t M cache table u J relation (high 168) (high 177) left h out ∧
      EntryInvariant vars u J out ∧
      ∃ k ≤ headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A,
      ∃ rr, Eval (headStep produce) k (machine regs (Product.working e left [] []) high)
        (machine rr (Product.working e out [] []) (afterHead high h tail)) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let c := headContext high h
  let hh := headHigh high h tail
  obtain ⟨r1,h1⟩ := startHead_eval regs (Product.working e left [] []) high h tail
    hsource h164 h176 h178 h175 h160
  have hc : c.Matches hh := by
    simp [c,hh,headContext,AssignmentContext.Matches,headHigh,headHigh3,headHigh2,headHigh1]
  have ht : hh 164 = [] := by simp [hh,headHigh,headHigh3,headHigh2,headHigh1,h164]
  have hsame : assignmentStream hh (rawFrames h.assignments) = hh :=
    assignmentStream_self hh _ (headHigh_assignments high h tail)
      (by simp [hh,headHigh,headHigh3,headHigh2,headHigh1,h174])
  obtain ⟨sum,hr,hsi,na,ha,r2,h2⟩ := assignmentScan_eval produce p t M cache hz table degree width hd hw
    vars u J relation validFrame H A contract c hh hc ht h.assignments hv left [] r1
    hl (entryInvariant_empty vars u J) hsize.2.2.2.2.2
  rw [hsame] at h2
  obtain ⟨nf,hf,r3,h3⟩ := finishHead_eval p t M cache hz table degree width hd hw u J left
    sum (assignmentStream hh []) r2 (by simp [assignmentStream,ht])
  have hb := finishHeadBudget_le p t M cache table vars u J left sum (assignmentStream hh []) H hl hsi
    (by simpa [hh,assignmentStream,headHigh,headHigh3,headHigh2,headHigh1] using hsize.2.2.1)
    (by simpa [hh,assignmentStream,headHigh,headHigh3,headHigh2,headHigh1] using hsize.2.1)
  have ho : EntryInvariant vars u J (Product.run p t M cache table u J left sum []) :=
    ⟨Product.run_valid p t M cache table vars u J left sum [] hl.1 hsi.1 (by simp),
      Product.run_nodup p t M cache table u J left sum [] (by simp [Sparse.keys])⟩
  refine ⟨_,⟨sum,hr,rfl⟩,ho,headHeaderBudget h+(na+nf),?_,r3,?_⟩
  · have hc := Nat.mul_le_mul_right
      (assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A+2)
      hsize.2.2.2.2.1
    rcases hsize with ⟨hbits,hmask,hcontext,hassignments,hcount,hx⟩
    dsimp [headHeaderBudget,headEnvelope]
    omega
  · simpa only [headStep,afterHead,c,hh,e] using h1.seq (h2.seq h3)

theorem headScan_eval (base : Fin 768 → List Bool)
    (h164 : base 164 = []) (h176 : base 176 = []) (h178 : base 178 = [])
    (h175 : base 175 = []) (h160 : base 160 = []) (h174 : base 174 = [])
    (hs : List HeadInput) (X : ℕ) (hsize : ∀ h ∈ hs, HeadSize H X h)
    (hv : HeadFrames validFrame base hs)
    (left : Raw p t (n:=n) (d:=d)) (regs : Fin 40 → Bool) (hl : EntryInvariant vars u J left) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, HeadsRel p t M cache table u J relation (base 168) (base 177) hs left out ∧
      EntryInvariant vars u J out ∧
      ∃ k ≤ hs.length*(headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A+2)+2,
      ∃ rr, Eval (headScan produce) k
        (machine regs (Product.working e left [] []) (Function.update base 161 (rawFrames (hs.map HeadInput.bits))))
        (machine rr (Product.working e out [] []) (Function.update base 161 [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let inv := fun (a : Raw p t (n:=n) (d:=d)) (tapes : Fin 768 → List Bool) =>
    EntryInvariant vars u J a ∧ ∃ source, source.length ≤ (rawFrames (hs.map HeadInput.bits)).length ∧ tapes =
      (machine (fun _ => false) (Product.working e a [] []) (Function.update base 161 source)).stacks
  have body : BodyContract 161 (headStep produce) HeadInput.bits
      (HeadStep p t M cache table u J relation (base 168) (base 177))
      (headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A)
      inv (fun h => h ∈ hs) := by
    intro a h tail state hmem hi hsrc
    obtain ⟨hai,source,hlen,htapes⟩ := hi
    have hsource : source = Encoding.frame h.bits ++ tail := by
      have he := (congrFun htapes 161).symm.trans hsrc
      simpa [machine] using he
    subst source
    have htail : tail.length ≤ (rawFrames (hs.map HeadInput.bits)).length := by
      simp only [List.length_append] at hlen
      omega
    let high := Function.update base 161 (Encoding.frame h.bits ++ tail)
    have heq : state = machine state.regs (Product.working e a [] []) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    obtain ⟨b,hr,hbi,k,hk,rr,he⟩ := headStep_eval produce p t M cache hz table degree width hd hw
      vars u J relation validFrame H A contract a high state.regs h tail X hai (hsize h hmem)
      (by simp [high]) (by simp [high,h164]) (by simp [high,h176])
      (by simp [high,h178]) (by simp [high,h175]) (by simp [high,h160]) (by simp [high,h174])
      (by simpa [high,headHigh_update161] using hv h hmem tail htail)
    have hfinished : afterHead high h tail = Function.update base 161 tail := by
      rw [afterHead_eq high h tail (by simp [high,h176]) (by simp [high,h178])
        (by simp [high,h175]) (by simp [high,h160]) (by simp [high,h174])]
      simp [high]
    let out := machine rr (Product.working e b [] []) (Function.update base 161 tail)
    refine ⟨b,?_,k,hk,out,⟨hbi,tail,htail,rfl⟩,?_,?_⟩
    · simpa [high] using hr
    · simp [out,machine]
    · rw [heq]
      simpa only [hfinished,out] using he
  obtain ⟨out,hr,k,hk,state,hi,hsrc,he⟩ := rawScan_eval 161 (headStep produce) HeadInput.bits
    (HeadStep p t M cache table u J relation (base 168) (base 177))
    (headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A)
    inv (fun h => h ∈ hs) body hs left
    (machine regs (Product.working e left [] []) (Function.update base 161 (rawFrames (hs.map HeadInput.bits))))
    (fun _ h => h) ⟨hl,_,le_rfl,rfl⟩ (by simp [machine,streamBits])
  obtain ⟨hout,source,hlen,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 161).symm.trans hsrc
    simpa [machine] using hh
  have heq : state = machine state.regs (Product.working e out [] []) (Function.update base 161 []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [htapes,hsource]
      rfl
  refine ⟨out,hr,hout,k,hk,state.regs,?_⟩
  rw [heq] at he
  exact he
end Native
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable

end OAI.Algorithms
