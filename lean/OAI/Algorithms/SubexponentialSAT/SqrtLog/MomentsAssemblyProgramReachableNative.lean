import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableModel

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

theorem assignmentScan_eval (c : AssignmentContext) (base : Fin 768 → List Bool)
    (hc : c.Matches base) (htmp : base 164 = [])
    (xs : List (List Bool)) (hv : AssignmentFrames validFrame base xs) (left seed : Raw p t (n:=n) (d:=d)) (regs : Fin 40 → Bool)
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
    EntryInvariant vars u J a ∧ ∃ source, source.length ≤ (rawFrames xs).length ∧ tapes =
      (machine (fun _ => false) (Product.working e left [] a) (assignmentStream base source)).stacks
  have body : BodyContract 160 (assignmentStep produce) id
      (AssignmentStep p t M cache table relation c)
      (assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A)
      inv (fun x => x ∈ xs) := by
    intro a x tail state hmem hi hsrc
    obtain ⟨hai,source,hlen,htapes⟩ := hi
    have hsource : source = Encoding.frame x ++ tail := by
      have he := (congrFun htapes 160).symm.trans hsrc
      simpa [machine,assignmentStream] using he
    subst source
    have htail : tail.length ≤ (rawFrames xs).length := by
      simp only [List.length_append] at hlen
      omega
    let high := assignmentStream base (Encoding.frame x ++ tail)
    have heq : state = machine state.regs (Product.working e left [] a) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    obtain ⟨b,hr,hbi,k,hk,rr,he⟩ := assignmentStep_eval produce p t M cache hz table degree width hd hw
      vars u J relation validFrame H A contract c x tail left a high state.regs hl hai (hx x hmem)
      (by simpa [AssignmentContext.Matches,high,assignmentStream] using hc)
      (by simp [high,assignmentStream]) (by simp [high,assignmentStream])
      (by simp [high,assignmentStream,htmp])
      (by simpa [high,assignmentHigh_stream] using hv tail htail x hmem)
    let out := machine rr (Product.working e left [] b) (assignmentStream base tail)
    refine ⟨b,hr,k,hk,out,⟨hbi,tail,htail,rfl⟩,?_,?_⟩
    · simp [out,machine,assignmentStream]
    · rw [heq]
      simpa only [high,assignmentHigh_finished,out] using he
  obtain ⟨out,hr,k,hk,state,hi,hsrc,he⟩ := rawScan_eval 160 (assignmentStep produce) id
    (AssignmentStep p t M cache table relation c)
    (assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A)
    inv (fun x => x ∈ xs) body xs seed
    (machine regs (Product.working e left [] seed) (assignmentStream base (rawFrames xs))) (fun _ h => h)
    ⟨hs,_,le_rfl,rfl⟩ (by simp [machine,assignmentStream,streamBits])
  obtain ⟨hout,source,hlen,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 160).symm.trans hsrc
    simpa [machine,assignmentStream] using hh
  have heq : state = machine state.regs (Product.working e left [] out) (assignmentStream base []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · simpa [machine, hsource] using htapes
  refine ⟨out,hr,hout,k,hk,state.regs,?_⟩
  rw [heq] at he
  exact he
end Native
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable

end OAI.Algorithms
