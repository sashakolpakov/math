import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelScan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram
  _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

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

theorem assignmentStep_eval (c : AssignmentContext) (x tail : List Bool)
    (left seed : Raw p t (n:=n) (d:=d)) (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hl : EntryInvariant vars u J left) (hs : EntryInvariant vars u J seed) (hx : x.length ≤ H)
    (hc : c.Matches high) (hsrc : high 160 = Encoding.frame x ++ tail)
    (h174 : high 174 = []) (h164 : high 164 = [])
    (hv : validFrame (assignmentHigh high x tail)) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, AssignmentStep p t M cache table relation c seed x out ∧ EntryInvariant vars u J out ∧
      ∃ k ≤ assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A,
      ∃ rr, Eval (assignmentStep produce) k
        (machine regs (Product.working e left [] seed) high)
        (machine rr (Product.working e left [] out) (Function.update (assignmentHigh high x tail) 174 [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := Product.working e left [] seed
  let rh := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  let high' := assignmentHigh high x tail
  have h1 := takeFrame_eval (machine regs a high) 160 174 (by decide) (by decide) (by decide)
    x tail (by simpa [machine] using hsrc) (by simpa [machine] using h164)
    (by simpa [machine] using h174)
  rw [afterTake_machine regs a high 160 174 (by decide) (by decide)] at h1
  have h1' : Eval (takeFrame 160 174 (by decide)) (9*x.length+7)
      (machine regs a high) (machine rh a high') := h1
  have hc' : c.Matches high' := by
    simpa [AssignmentContext.Matches,high',assignmentHigh] using hc
  obtain ⟨value,hr,hj,np,hp,rp,he⟩ := contract c x left seed high' rh hl hs hv hc'
    (by simp [high',assignmentHigh])
  let outputHigh := Function.update high' 174 []
  obtain ⟨nw,hw',rw,he'⟩ := weightedAdd_machine_eval p t M cache hz table degree width hd hw
    u J (Product.bytes left) value.1 value.2 seed outputHigh rp
  let out := weightedValue p t M cache table value.1 value.2 seed
  have hclear := clear_right_eval rw
    (weightedStore e (Product.bytes left) (Product.bytes out) (Product.bytes value.2) []) outputHigh
  have hjs := entryInvariant_sizes vars u J value.2 hj
  have hss := entryInvariant_sizes vars u J seed hs
  have hb := weightedBudget_le p t M cache table value.1 value.2 seed (n+u+J)
    (2*dictionaryCapacity vars u J) (entryInvariant_keyBound vars u J _ hj)
    (entryInvariant_keyBound vars u J seed hs) (by omega)
  refine ⟨out,⟨value,hr,rfl⟩,entryInvariant_weighted p t M cache table vars u J _ _ _ hj hs,
    (9*x.length+7)+(np+(nw+(2*(Product.bytes value.2).length+3))),?_,
    SubexponentialSAT.BitProgram.readRegs rw 0 1 none,?_⟩
  · dsimp [assignmentEnvelope]; omega
  · convert h1'.seq (he.seq (he'.seq hclear)) using 1 <;>
      simp [assignmentStep,e,high',outputHigh,out,weightedStore,
        Product.working,Product.environment,Product.idle,Product.bytes,
        MomentsProgram.Normalize.bytes,Squarefree.Program.rawEntries,
        Squarefree.Program.encodeDictionary]

theorem assignmentScan_eval (c : AssignmentContext) (base : Fin 768 → List Bool)
    (hc : c.Matches base) (htmp : base 164 = [])
    (hv : ∀ source x, validFrame (Function.update (Function.update base 160 source) 174 x))
    (xs : List (List Bool)) (left seed : Raw p t (n:=n) (d:=d)) (regs : Fin 40 → Bool)
    (hl : EntryInvariant vars u J left) (hs : EntryInvariant vars u J seed)
    (hx : ∀ x ∈ xs, x.length ≤ H) :
    let e := Product.environment p t M cache table degree width u J
    ∃ out, HeadRel p t M cache table relation c xs seed out ∧ EntryInvariant vars u J out ∧
      ∃ k ≤ xs.length*(assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A+2)+2,
      ∃ rr, Eval (assignmentScan produce) k
        (machine regs (Product.working e left [] seed) (assignmentStream base (rawFrames xs)))
        (machine rr (Product.working e left [] out) (assignmentStream base [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let inv := fun (a : Raw p t (n:=n) (d:=d)) (tapes : Fin 768 → List Bool) =>
    EntryInvariant vars u J a ∧ ∃ source, tapes =
      (machine (fun _ => false) (Product.working e left [] a) (assignmentStream base source)).stacks
  have body : BodyContract 160 (assignmentStep produce) id
      (AssignmentStep p t M cache table relation c)
      (assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A)
      inv (fun x => x.length ≤ H) := by
    intro a x tail state hxl hi hsrc
    obtain ⟨hai,source,htapes⟩ := hi
    have hsource : source = Encoding.frame x ++ tail := by
      have he := (congrFun htapes 160).symm.trans hsrc
      simpa [machine,assignmentStream] using he
    subst source
    let high := assignmentStream base (Encoding.frame x ++ tail)
    have heq : state = machine state.regs (Product.working e left [] a) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    obtain ⟨b,hr,hbi,k,hk,rr,he⟩ := assignmentStep_eval produce p t M cache hz table degree width hd hw
      vars u J relation validFrame H A contract c x tail left a high state.regs hl hai hxl
      (by simpa [AssignmentContext.Matches,high,assignmentStream] using hc)
      (by simp [high,assignmentStream]) (by simp [high,assignmentStream])
      (by simp [high,assignmentStream,htmp])
      (by simpa [high,assignmentHigh_stream] using hv tail x)
    let out := machine rr (Product.working e left [] b) (assignmentStream base tail)
    refine ⟨b,hr,k,hk,out,⟨hbi,tail,rfl⟩,?_,?_⟩
    · simp [out,machine,assignmentStream]
    · rw [heq]
      simpa only [high,assignmentHigh_finished,out] using he
  obtain ⟨out,hr,k,hk,state,hi,hsrc,he⟩ := rawScan_eval 160 (assignmentStep produce) id
    (AssignmentStep p t M cache table relation c)
    (assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A)
    inv (fun x => x.length ≤ H) body xs seed
    (machine regs (Product.working e left [] seed) (assignmentStream base (rawFrames xs))) hx
    ⟨hs,_,rfl⟩ (by simp [machine,assignmentStream,streamBits])
  obtain ⟨hout,source,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 160).symm.trans hsrc
    simpa [machine,assignmentStream] using hh
  subst source
  have heq : state = machine state.regs (Product.working e left [] out) (assignmentStream base []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact htapes
  refine ⟨out,hr,hout,k,hk,state.regs,?_⟩
  rw [heq] at he
  exact he
end Native
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
