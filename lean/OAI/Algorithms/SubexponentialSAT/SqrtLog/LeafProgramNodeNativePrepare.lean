import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeFrame

namespace OAI.Algorithms

/-! Physical node preparation, with no supplied head builder or support list. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls
open LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev HeadInputs := LeafHeadSetupProgram.Native.Inputs

def loadedState (a : Data) : Data :=
  ⟨a.regs,(LayoutMasters.loaded (LayoutMasters.project a)).stacks⟩

/-- These hypotheses describe only the parked input words and blank working
storage. The displayed loaded state is the pure specification of paid copies. -/
structure Ready (s : HeadInputs) (a : Data) : Prop where
  blank : Blank a
  heads : Native.Ready s (Native.project (loadedState a))

structure HeadEvidence (s : HeadInputs) (a b : Data) where
  ra : Fin 3 → Bool
  rd : Fin 8 → Bool
  rc : Fin 8 → Bool
  words : List (List Bool)
  tables : List BucketTupleProgram.HeadTable
  costs : List ℕ
  steps : ℕ
  cache : CacheCorrect s.height (unary s.R) s.width words
  produced : ProducedHeads (Native.start s (Native.project a) ra rd rc words)
    s.n s.N s.D s.rows s.low s.relation s.columnLength (s.node.val*s.r) tables
  count : tables.length=s.r
  costs_count : costs.length=s.r
  run : Eval Node.heads steps a b
  buckets : b.stacks 163=MomentsAssembly.bucketsInput
    (((BucketTupleProgram.enumerate tables).map (BucketTupleProgram.Representative.bucket s.n)).reverse)
  frame : ∀ i,External i→b.stacks i=a.stacks i
  private_clean : ∀ i : Fin 768,640 ≤ i.val ∧ i.val < 680→b.stacks i=[]
  work_clean : ∀ i : Fin 288,b.stacks (workPort (by decide) i)=[]
  positive : b.stacks 710=words.flatten++a.stacks 710
  negative : b.stacks 711=List.replicate (s.R*s.width.length) false++a.stacks 711
  denominator : b.stacks 712=s.power.1++a.stacks 712
  registers : ∀ i : Fin 40,16 ≤ i.val→b.regs i=a.regs i
  paid : ∃ loopEnd rf,
    CostTrace Native.entry (Native.start s (Native.project a) ra rd rc words)
      s.n s.N s.D (s.Q*s.r) s.rows s.low s.relation s.columnTime s.columnLength
      (s.node.val*s.r) [[]] tables costs (Native.start s (Native.project a) ra rd rc words) loopEnd ∧
    b=embedState wideRegisters id a
      (SubexponentialSAT.SubexpSetupStorage.clearManyState cleanupPorts
        (finalResult loopEnd rf (unary s.n) (BucketTupleProgram.enumerate tables))) ∧
    steps ≤ nodeCost (Native.project a) ra rd rc s.n s.r s.node.val s.records s.height (unary s.R)
      s.width words tables costs loopEnd rf+1 ∧
    loopEnd.stacks 660=BucketTupleProgram.Representative.tuplesBits (BucketTupleProgram.enumerate tables) ∧
    loopEnd.stacks 128=unary s.n

theorem heads_execute (s : HeadInputs) (a : Data) (ha : Native.Ready s (Native.project a)) :
    ∃ b,Nonempty (HeadEvidence s a b) := by
  obtain ⟨ra,rd,rc,words,tables,costs,steps,b,hc,hp,ht,hn,he,hb,hf,hw,hm,hpos,hneg,hden,hr,hpaid⟩ :=
    Native.wide_command_eval s a ha
  exact ⟨b,⟨⟨ra,rd,rc,words,tables,costs,steps,hc,hp,ht,hn,he,hb,hf,hw,hm,hpos,hneg,hden,hr,hpaid⟩⟩⟩

theorem ready_congr (s : HeadInputs) {a b : Data} (hs : a.stacks=b.stacks)
    (ha : Native.Ready s (Native.project a)) : Native.Ready s (Native.project b) := by
  cases ha
  constructor <;> simp_all only [Native.project,projectState]

theorem load_execute (s : HeadInputs) (a : Data) (ha : Ready s a) :
    ∃ b,Eval LayoutMasters.load (LayoutMasters.loadCost (LayoutMasters.project a)+1) a b ∧
      b.stacks=(loadedState a).stacks ∧ Native.Ready s (Native.project b) ∧
      (∀ i : Fin 40,16 ≤ i.val→b.regs i=a.regs i) := by
  have ht : a.stacks 684=[] := ha.blank 684 ((Node.mem_cleanup _).mpr (by norm_num)) (by decide)
  obtain ⟨b,he,hs,hr⟩ := LayoutMasters.load_eval a ht
  exact ⟨b,he,hs,ready_congr s hs.symm ha.heads,hr⟩

theorem cache_external {i : Fin 768} (hi : i∈LeafNodeCacheProgram.cachePorts) :
    External i ∧ i≠78 := by
  simp only [LeafNodeCacheProgram.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [External,Fin.ext_iff]

theorem head_cache_ready (s : HeadInputs) {a a' b : Data} (ha : Ready s a)
    (hl : a'.stacks=(loadedState a).stacks) (h : HeadEvidence s a' b) :
    LeafNodeCacheProgram.Ready b.stacks := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · rw [h.frame i (cache_external hi).1,hl]
    exact (LayoutMasters.loaded_frame (LayoutMasters.project a) i (cache_not_low hi)).trans
      (ha.blank i (cache_mem_cleanup hi) (cache_external hi).2)
  · have hb : 340 ≤ i.val ∧ i.val < 628 := by
      simp only [LeafNodeCacheProgram.pocket,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
    let j : Fin 288 := ⟨i.val-340,by omega⟩
    have heq : workPort (by decide) j=i := by apply Fin.ext; dsimp [workPort,j]; omega
    simpa only [heq] using h.work_clean j

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
