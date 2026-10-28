import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativePrepare

namespace OAI.Algorithms

/-! The actual cache and support producers complete physical node preparation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls
open LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem not_low_of_ge {i : Fin 768} (hi : 142 ≤ i.val) : i ∉ LayoutMasters.lowPorts := by
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  have hv := congrArg Fin.val hj
  change 128+j.val=i.val at hv
  have := j.isLt
  omega

theorem cache_lt {i : Fin 768} (hi : i∈LeafNodeCacheProgram.cachePorts) : i.val < 192 := by
  simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

theorem cache_support_ready (s : HeadInputs) {a a' b c : Data} (ha : Ready s a)
    (hl : a'.stacks=(loadedState a).stacks) (hh : HeadEvidence s a' b)
    (hc : c.stacks=LeafNodeCacheProgram.cacheTapes (LeafNodeCacheProgram.project b)) :
    LeafSupportInputProgram.Ready c := by
  constructor
  · rw [hc,LeafNodeCacheProgram.cache_frame _ 169 (by decide)]
    change b.stacks 169=[]
    rw [hh.frame 169 (by norm_num [External,Fin.ext_iff]),hl]
    exact (LayoutMasters.loaded_frame (LayoutMasters.project a) 169 (not_low_of_ge (by norm_num))).trans
      (ha.blank 169 ((Node.mem_cleanup _).mpr (by norm_num)) (by decide))
  · intro j
    let i := LeafSupportInputProgram.privatePorts j
    have hib : 340 ≤ i.val ∧ i.val < 350 := by
      dsimp [i]
      fin_cases j <;> decide
    have hnc : i ∉ LeafNodeCacheProgram.cachePorts := by
      intro hm
      have := cache_lt hm
      omega
    rw [hc,LeafNodeCacheProgram.cache_frame _ _ hnc]
    let k : Fin 288 := ⟨i.val-340,by omega⟩
    have heq : workPort (by decide) k=i := by apply Fin.ext; dsimp [workPort,k]; omega
    exact heq ▸ hh.work_clean k

structure Preparation (s : HeadInputs) (a d : Data) where
  loaded : Data
  headEnd : Data
  cacheEnd : Data
  head : HeadEvidence s loaded headEnd
  supports : List (Finset (Fin s.n))
  supportSteps : ℕ
  load_run : Eval LayoutMasters.load (LayoutMasters.loadCost (LayoutMasters.project a)+1) a loaded
  loaded_words : loaded.stacks=(loadedState a).stacks
  cache_run : Eval LeafNodeCacheProgram.command (LeafNodeCacheProgram.budget headEnd) headEnd cacheEnd
  cached_words : cacheEnd.stacks=LeafNodeCacheProgram.cacheTapes (LeafNodeCacheProgram.project headEnd)
  support_run : Eval Node.supports supportSteps cacheEnd d
  support_bound : supportSteps ≤ LeafSupportInputProgram.cost s.n (a.stacks 243).length
  supports_nodup : supports.Nodup
  supports_all : ∀ S,S∈supports ↔ S.card < (a.stacks 243).length
  supports_count : supports.length=SupportProgram.count s.n (a.stacks 243).length
  support_words : d.stacks 169=MomentsAssembly.rawFrames (supports.map Squarefree.encodeMask)
  support_frame : ∀ i,i≠169→d.stacks i=cacheEnd.stacks i
  buckets : d.stacks 163=MomentsAssembly.bucketsInput
    (((BucketTupleProgram.enumerate head.tables).map (BucketTupleProgram.Representative.bucket s.n)).reverse)
  frame : ∀ i,i∉Node.cleanupPorts→d.stacks i=a.stacks i
  registers : ∀ i : Fin 40,16 ≤ i.val→d.regs i=a.regs i

def Preparation.steps {s : HeadInputs} {a d : Data} (p : Preparation s a d) : ℕ :=
  LayoutMasters.loadCost (LayoutMasters.project a)+1+p.head.steps+
    LeafNodeCacheProgram.budget p.headEnd+p.supportSteps

theorem prepare (s : HeadInputs) (a : Data) (ha : Ready s a) :
    ∃ d,Nonempty (Preparation s a d) := by
  obtain ⟨a',hl,hls,hr,hregL⟩ := load_execute s a ha
  obtain ⟨b,⟨hh⟩⟩ := heads_execute s a' hr
  obtain ⟨c,hc,hcs,hregC⟩ := LeafNodeCacheProgram.command_eval b (head_cache_ready s ha hls hh)
  have hcframe (i : Fin 768) (hi : i∉Node.cleanupPorts) : c.stacks i=a.stacks i := by
    rw [hcs,LeafNodeCacheProgram.cache_frame _ i (fun hm=>hi (cache_mem_cleanup hm))]
    change b.stacks i=a.stacks i
    rw [hh.frame i (not_cleanup_head_external hi),hls]
    exact LayoutMasters.loaded_frame (LayoutMasters.project a) i (not_cleanup_not_low hi)
  have hn : (c.stacks 128).length=s.n := by
    rw [hcs,LeafNodeCacheProgram.cache_frame _ 128 (by decide)]
    change (b.stacks 128).length=s.n
    rw [hh.frame 128 (by norm_num [External,Fin.ext_iff]),hls]
    have h128 : (loadedState a).stacks 128=unary s.n := ha.heads.ambient
    simp [h128, unary]
  have hJ : (c.stacks 243).length=(a.stacks 243).length := congrArg List.length
    (hcframe 243 (by rw [Node.mem_cleanup]; norm_num))
  have hs := LeafSupportInputProgram.program_runsIn c (cache_support_ready s ha hls hh hcs)
  rw [hn,hJ] at hs
  obtain ⟨d,ss,hsn,hsa,hsc,hso,hsf,hsr,ks,hks,hst⟩ := hs
  have hse : Eval Node.supports ks c d := Eval.call _ hst
  have hbucket : d.stacks 163=MomentsAssembly.bucketsInput
      (((BucketTupleProgram.enumerate hh.tables).map (BucketTupleProgram.Representative.bucket s.n)).reverse) := by
    rw [hsf 163 (by decide),hcs,LeafNodeCacheProgram.cache_frame _ 163 (by decide)]
    exact hh.buckets
  refine ⟨d,⟨⟨a',b,c,hh,ss,ks,hl,hls,hc,hcs,hse,hks,hsn,hsa,hsc,hso,hsf,hbucket,?_,?_⟩⟩⟩
  · intro i hi
    have hn169 : i≠169 := by intro he; subst i; exact hi ((Node.mem_cleanup _).mpr (by norm_num))
    exact (hsf i hn169).trans (hcframe i hi)
  · intro i hi
    have h10 : 10 ≤ i.val := le_trans (by decide : 10 ≤ 16) hi
    exact (hsr i h10).trans ((hregC i hi).trans ((hh.registers i hi).trans (hregL i hi)))

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
