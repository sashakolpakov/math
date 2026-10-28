import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeDense
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableReadout

namespace OAI.Algorithms

/-! The fixed physical node using frame facts only for reachable loop inputs.
The command, costs, typed output relation and exact final frame are unchanged. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem execute_of_reachable_assignment_contract (s : HeadInputs) (a b : Data) (pr : Preparation s a b)
    (ha : Ready s a) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d  →  Fin d  →  Fin d  →  Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (one zero : RingProgram.Code (Word (baseWidth p t)) d)
    (h194 : a.stacks 194=M.bits) (h201 : a.stacks 201=RingTriple.tableEncoding table)
    (h202 : a.stacks 202=width) (h203 : a.stacks 203=cache.zero.val)
    (h204 : a.stacks 204=degree) (h212 : a.stacks 212=List.replicate u true)
    (h243 : a.stacks 243=List.replicate J true)
    (h207 : a.stacks 207=RingProgram.flat one) (h280 : a.stacks 280=RingProgram.flat zero)
    (h102 : a.stacks 102=[])
    (relation : AssignmentContext  →  List Bool  →  Contribution s.n (baseWidth p t) d  →  Prop)
    (validFrame : (Fin 768  →  List Bool)  →  Prop) (H X Y A W : ℕ)
    (contract : Relational.AssignmentContract p t M cache table u J relation Factor.assignment
      degree width Finset.univ validFrame A)
    (hsize : ∀ v∈pr.bucketInputs,BucketSize H X Y v)
    (hbytes : (b.stacks 169).length ≤ H)
    (hvalid : Relational.Reachable.BucketFrames (baseWidth p t) d
      (Finset.univ : Finset (Fin s.n)) u J validFrame b.stacks pr.supports pr.bucketInputs)
    (hworkspace : ∀ i∈Node.cleanupPorts,(b.stacks i).length ≤ W)
    (hdict : dictionaryByteEnvelope (baseWidth p t) d (s.n+u+J)
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J) ≤ W) :
    ∃ entries, Relational.BucketsRel p t M cache table u J relation pr.supports
      (originEntries one) pr.bucketInputs [] entries ∧ EntryInvariant Finset.univ u J entries ∧
    ∃ time ≤ fullBudget pr (baseWidth p t) d u J H X Y A W, ∃ rr,
      Eval Node.command time a
        ⟨rr,Function.update (Function.update a.stacks 78 []) 102
          (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J)⟩ ∧
      ∀ i : Fin 40,16 ≤ i.val → rr i=a.regs i := by
  let e := emptyCore (Product.environment p t M cache table degree width u J)
  have hcore : ∀ i : Fin 56,b.stacks (corePorts i)=Product.tapes e i :=
    pr.core_words ha p t M cache table degree width u J h194 h201 h202 h203 h204 h212 h243
  have h166 : b.stacks 166=[] := pr.empty_word ha 166
    ((Node.mem_cleanup _).mpr (by norm_num)) (not_low_of_ge (by norm_num))
    (by decide) (by decide)
  have hstart : machine b.regs e (bucketStream b.stacks (Product.bytes
      ([] : List (Product.Entry s.n (baseWidth p t) d))) (bucketsInput pr.bucketInputs))=b := by
    have hh : bucketStream b.stacks (Product.bytes
        ([] : List (Product.Entry s.n (baseWidth p t) d))) (bucketsInput pr.bucketInputs)=b.stacks := by
      funext i
      by_cases h163 : i=163
      · subst i; simpa [bucketStream,Preparation.bucketInputs] using pr.buckets.symm
      by_cases h166' : i=166
      · subst i; simp [bucketStream,Product.bytes,Normalize.bytes,
          Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary,h166]
      simp [bucketStream,h163,h166']
    rw [hh]
    exact machine_self b e hcore
  obtain ⟨entries,hrel,hinv,k,hk,rr,he,hr⟩ :=
    Relational.Reachable.denseCommand_eval_framed Factor.assignment p t M cache hz table degree width hd hw
      Finset.univ u J relation validFrame H A contract (originEntries one) [] pr.supports
      pr.bucketInputs b.stacks b.regs X Y pr.supports.length pr.bucketInputs.length
      (originEntries_valid one Finset.univ u J hu hJ) (entryInvariant_empty Finset.univ u J)
      hsize le_rfl le_rfl hbytes pr.support_words (pr.one_entries ha one h207).2
      (pr.support_clean ha)
      (pr.empty_word ha 162 ((Node.mem_cleanup _).mpr (by norm_num))
        (not_low_of_ge (by norm_num)) (by decide) (by decide))
      (pr.empty_word ha 170 ((Node.mem_cleanup _).mpr (by norm_num))
        (not_low_of_ge (by norm_num)) (by decide) (by decide))
      (pr.empty_word ha 177 ((Node.mem_cleanup _).mpr (by norm_num))
        (not_low_of_ge (by norm_num)) (by decide) (by decide)) hvalid zero (unary s.n)
      (by simp [unary]) (pr.output_empty h102) (pr.zero_word ha zero h280) (pr.shape_word ha)
      (pr.readout_clean ha) LeafAssignmentRegisterFrame.assignment
  let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
  let finish := resultState b rr (Product.bytes entries) bits
  have hm : Eval Node.moments k b finish := by
    change Eval (denseCommand Factor.assignment) k b
      (resultState b rr (Product.bytes entries) bits)
    rw [hstart,resultState_machine b e rr (Product.bytes entries) bits hcore] at he
    exact he
  have hb := resultState_cleanup_bound b rr (Product.bytes entries) bits W hworkspace
    ((entryInvariant_sizes Finset.univ u J entries hinv).2.trans hdict)
  have hall := Node.command_eval a pr.loaded pr.headEnd pr.cacheEnd b finish
    (LayoutMasters.loadCost (LayoutMasters.project a)+1) pr.head.steps
    (LeafNodeCacheProgram.budget pr.headEnd) pr.supportSteps k
    pr.load_run pr.head.run pr.cache_run pr.support_run hm
  have hout : Node.cleaned finish =
      ⟨(Node.cleaned finish).regs,Function.update (Function.update a.stacks 78 []) 102 bits⟩ := by
    generalize hclean : Node.cleaned finish = clean
    cases clean with
    | mk regs stackWords =>
      have hs := cleaned_resultState pr ha rr (Product.bytes entries) bits
      rw [hclean] at hs
      change stackWords = Function.update (Function.update a.stacks 78 []) 102 bits at hs
      rw [hs]
  rw [hout] at hall
  refine ⟨entries,hrel,hinv,_,?_,_,hall,?_⟩
  · dsimp [fullBudget]
    have hs := pr.support_bound
    change Node.cleanupCost finish ≤ Node.cleanupPorts.length*(2*W+3) at hb
    omega
  · intro i hi
    exact (cleaned_register finish i hi).trans ((hr i hi).trans (pr.registers i hi))

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
