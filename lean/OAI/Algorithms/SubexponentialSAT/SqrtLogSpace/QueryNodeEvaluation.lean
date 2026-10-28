import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAddressedTarget

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- This is the exact prefix of the fixed node body, before its pair loop. -/
def prepareNode : Code :=
  .seq QueryAssembler.Nodes.beginNode
    (.seq NativeLayoutLoad.command
      (.seq QueryStreamProgram.bootstrapNode PairNativeSetup.setupCaller))

noncomputable def loadedNode (a : Data) (bits : List Bool) (tail : List (List Bool)) : Data :=
  NativeLayoutLoad.result (QueryAssembler.Nodes.begunNode a bits tail)

/-- Reading the current node leaves the parked source bank and node index intact. -/
theorem begun_sourceBank (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool)) (h : NativeLayoutLoad.SourceBank s a) :
    NativeLayoutLoad.SourceBank s (QueryAssembler.Nodes.begunNode a bits tail) := by
  have hf := QueryAssembler.Nodes.begunNode_frame a bits tail
  exact ⟨(hf 730 (by decide)).trans h.ambient,
    (hf 731 (by decide)).trans h.factors,(hf 732 (by decide)).trans h.colors,
    (hf 733 (by decide)).trans h.nodes,(hf 734 (by decide)).trans h.wordWidth,
    (hf 735 (by decide)).trans h.words,(hf 736 (by decide)).trans h.low,
    (hf 737 (by decide)).trans h.metadata,(hf 738 (by decide)).trans h.plans,
    (hf 740 (by decide)).trans h.order,(hf 741 (by decide)).trans h.height,
    (hf 742 (by decide)).trans h.width,
    (congrArg BinaryArithmetic.toNat (hf 743 (by decide))).trans h.offset,
    (hf 307 (by decide)).trans h.node⟩

theorem loadedNode_ready (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool)) (h : NativeLayoutLoad.SourceBank s a) :
    Native.Ready s (projectState SignatureHeadLoader.leafRegs
      QueryAssembler.Nodes.lowPort (loadedNode a bits tail)) :=
  NativeLayoutLoad.result_ready s _ (begun_sourceBank s a bits tail h)

/-- The paid reset, rather than an entry assumption, empties the node sum and caches. -/
theorem loadedNode_empty (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i ∈ ([710,711,712,850,851] : List (Fin 896))) :
    (loadedNode a bits tail).stacks i=[] := by
  have hn : i ∉ NativeLayoutLoad.clearPorts := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  rw [loadedNode,NativeLayoutLoad.result_frame _ i hn,
    QueryAssembler.Nodes.begunNode_stacks]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp [QueryAssembler.Nodes.nodeResetPorts]

noncomputable def bootstrapped (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) : Data :=
  embedState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a
    (SignatureHeadLoader.bootstrapResult s
      (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) ra rd rc words)

theorem bootstrapped_low (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (i : Fin 768) :
    (bootstrapped s a ra rd rc words).stacks (QueryAssembler.Nodes.lowPort i)=
      (SignatureHeadLoader.bootstrapResult s
        (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) ra rd rc words).stacks i :=
  embedState_stack _ _ _ _ (Fin.castAdd_injective 768 128) i

theorem bootstrapped_high (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : 768 ≤ i.val) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

theorem bootstrapped_ready (s : Native.Inputs) (a : Data)
    (ha : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort
      (bootstrapped s a ra rd rc words)) := by
  rw [bootstrapped,projectState_embed SignatureHeadLoader.leafRegs
    QueryAssembler.Nodes.lowPort _ _ SignatureHeadLoader.leafRegs.injective
    (Fin.castAdd_injective 768 128)]
  exact QueryReadyConstruction.bootstrap_ready s _ ha ra rd rc words

/-- The actual finite bootstrap call creates its cache on the same returned
state. Its retained cap is fixed per source, independently of the node index. -/
theorem bootstrap_run (s : Native.Inputs) (a : Data) (B : ℕ)
    (ha : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B)
    (h710 : a.stacks 710=[]) (h711 : a.stacks 711=[]) (h712 : a.stacks 712=[]) :
    ∃ ra rd rc words ticks,
      CacheCorrect s.height (unary s.R) s.width words ∧
      ticks ≤ 20000*(B+1)^4+1 ∧
      Eval QueryStreamProgram.bootstrapNode ticks a (bootstrapped s a ra rd rc words) ∧
      WordBound B (bootstrapped s a ra rd rc words) := by
  have hp : WordBound B (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) :=
    fun i => hb (QueryAssembler.Nodes.lowPort i)
  obtain ⟨ra,rd,rc,words,ticks,hw,ht,hr,_hb,_hp⟩ :=
    SignatureHeadLoader.native_bootstrap_run_space s _ ha B hp
  have he := eval_call_from_state SignatureHeadLoader.bootstrapProgram
    SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a
    SignatureHeadLoader.leafRegs.injective (Fin.castAdd_injective 768 128) hr
  have hbound := SignatureHeadLoader.native_bootstrap_retained_bound s _ ha B hp
    ra rd rc words hw h710 h711 h712
  rw [max_eq_left hcap] at hbound
  refine ⟨ra,rd,rc,words,ticks,hw,ht,he,?_⟩
  intro i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val,hi⟩
    have hj : QueryAssembler.Nodes.lowPort j=i := Fin.ext rfl
    rw [←hj,bootstrapped_low]
    exact hbound j
  · rw [bootstrapped_high s a ra rd rc words i (by omega)]
    exact hb i

/-- The bootstrap touches neither the low query data nor the retained upper
masters outside its three deliberately replaced cache words. -/
theorem bootstrapped_frame (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : i.val<340 ∨ 700 ≤ i.val)
    (h710 : i ≠ 710) (h711 : i ≠ 711) (h712 : i ≠ 712) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : QueryAssembler.Nodes.lowPort j=i := Fin.ext rfl
    rw [←hj,bootstrapped_low]
    rcases hi with hi|hi
    · exact QueryReadyConstruction.bootstrap_low s _ ra rd rc words j hi
    · have hj710 : j ≠ 710 := fun h => h710 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj711 : j ≠ 711 := fun h => h711 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj712 : j ≠ 712 := fun h => h712 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj659 : j ≠ 659 := by intro h; have hh:=congrArg Fin.val h; change i.val=659 at hh; omega
      rw [SignatureHeadLoader.bootstrapResult,retainedState_frame _ j hj659 hj710 hj711 hj712]
      apply bootState_frame
      · exact ⟨Or.inr (by change 700 ≤ j.val at hi; omega),by
          intro h; have hh:=congrArg Fin.val h; change i.val=659 at hh; omega⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false]
        intro h
        rcases h with h|h|h|h|h|h|h
        all_goals have hh:=congrArg Fin.val h
        all_goals simp only [Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hh
        all_goals change 700 ≤ j.val at hi
        all_goals omega
  · exact bootstrapped_high s a ra rd rc words i (by omega)

/-- All interpolation arithmetic and frontend words in this list are kept
through the concrete node prefix. The three cache outputs are accounted for
separately because they are regenerated for this node. -/
def framePorts : List (Fin 896) :=
  [194,201,202,203,204,207,209,211,212,243,256,280,281,300,307,320,322,338,
    700,701,702,703,704,705,706,707,708,709,713,714,715,716,717,718,719,728,
    730,731,732,733,734,735,736,737,738,739,740,741,742,743,863]

theorem loadedNode_frame (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i ∈ framePorts) :
    (loadedNode a bits tail).stacks i=a.stacks i := by
  have hn : i ∉ NativeLayoutLoad.clearPorts ∧ i ∉ 301::QueryAssembler.Nodes.nodeResetPorts := by
    simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (NativeLayoutLoad.result_frame _ i hn.1).trans
    (QueryAssembler.Nodes.begunNode_frame a bits tail i hn.2)

theorem bootstrapped_framePorts (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : i ∈ framePorts) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  have hp : (i.val<340 ∨ 700 ≤ i.val) ∧ i ≠ 710 ∧ i ≠ 711 ∧ i ≠ 712 := by
    simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact bootstrapped_frame s a ra rd rc words i hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- The native readiness fields are all disjoint from pair initialization. -/
theorem ready_after_setup (s : Native.Inputs) (a b : Data)
    (h : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=a.stacks i) :
    Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort b) := by
  have hl (i : Fin 768) (hi : i ∈ ([128,129,130,131,132,133,134,135,136,138,139,140,141,307,660,665] : List (Fin 768))) :
      b.stacks (QueryAssembler.Nodes.lowPort i)=a.stacks (QueryAssembler.Nodes.lowPort i) := by
    apply hf
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    all_goals rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact ⟨(hl 128 (by decide)).trans h.ambient,(hl 129 (by decide)).trans h.factors,
    (hl 130 (by decide)).trans h.colors,(hl 131 (by decide)).trans h.nodes,
    (hl 132 (by decide)).trans h.wordWidth,(hl 133 (by decide)).trans h.words,
    (hl 134 (by decide)).trans h.low,(hl 135 (by decide)).trans h.metadata,
    (hl 136 (by decide)).trans h.plans,(hl 138 (by decide)).trans h.order,
    (hl 139 (by decide)).trans h.height,(hl 140 (by decide)).trans h.width,
    (congrArg BinaryArithmetic.toNat (hl 141 (by decide))).trans h.offset,
    (hl 307 (by decide)).trans h.node,(hl 660 (by decide)).trans h.tuples,
    (hl 665 (by decide)).trans h.marker⟩

/-- Exact node/cache words at the returned prefix state. The premises are
only the frame equations returned by its actual setup execution. -/
theorem prepared_words (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (b : Data)
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) :
    b.stacks 78=bits ∧ b.stacks 301=Encoding.encodeList id tail ∧
      (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
      b.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hp ∧
      b.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height).hn ∧
      b.stacks 712=s.power.1 := by
  have h78 := hf 78 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h301 := hf 301 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcache := QueryReadyConstruction.bootstrap_source_cache s
    (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort (loadedNode a bits tail))
    ra rd rc words (loadedNode_empty a bits tail 710 (by decide))
      (loadedNode_empty a bits tail 711 (by decide)) (loadedNode_empty a bits tail 712 (by decide))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [h78,bootstrapped_frame s _ ra rd rc words 78 (by decide) (by decide) (by decide) (by decide),
      loadedNode,NativeLayoutLoad.result_frame _ 78 (by decide),QueryAssembler.Nodes.begunNode_stacks]
    simp
  · rw [h301,bootstrapped_frame s _ ra rd rc words 301 (by decide) (by decide) (by decide) (by decide),
      loadedNode,NativeLayoutLoad.result_frame _ 301 (by decide),QueryAssembler.Nodes.begunNode_stacks]
    simp
  · intro i hi
    have hn : i ∉ PairNativeSetup.scratch ∧ i ≠ 832 ∧ i ≠ 833 ∧ i ≠ 834 ∧ i ≠ 835 := by
      simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    exact (hf i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((bootstrapped_framePorts s _ ra rd rc words i hi).trans (loadedNode_frame a bits tail i hi))
  · rw [hf 710 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (bootstrapped_low s _ ra rd rc words 710).trans hcache.1
  · rw [hf 711 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (bootstrapped_low s _ ra rd rc words 711).trans hcache.2.1
  · rw [hf 712 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (bootstrapped_low s _ ra rd rc words 712).trans hcache.2.2

/-- No successful layout or executable callback is assumed here: the parked
words determine native readiness, and the fixed prefix executes every read,
clear, copy and bootstrap before constructing the pair controllers. -/
theorem prepare_eval (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (H : Finset (Fin s.n)) (J B : ℕ)
    (hsource : NativeLayoutLoad.SourceBank s a)
    (hcursor : a.stacks 301=Encoding.encodeList id (bits::tail))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (horder : a.stacks 243=List.replicate J true)
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
    ∃ ra rd rc words ticks b,
      CacheCorrect s.height (unary s.R) s.width words ∧
      Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
      WordBound B b ∧
      Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort b) ∧
      b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate J true ∧
      b.stacks 834=[] ∧ b.stacks 835=[] ∧ b.stacks 850=[] ∧ b.stacks 851=[] ∧
      (∀ i ∈ PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
        b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) ∧
      Trace (compiled prepareNode 301 832) (ticks+1)
        (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
      ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
        (a.withPC (some (compiled prepareNode 301 832).entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1 := by
  have hencoded := hb 301
  rw [hcursor,Encoding.length_encodeList_cons] at hencoded
  have hbits : bits.length ≤ B := by simp only [id_eq] at hencoded; omega
  have htail : (Encoding.encodeList id tail).length ≤ B := by omega
  have hbegun := QueryAssembler.Nodes.begunNode_bound a bits tail B hb hbits htail
  have hloaded : WordBound B (loadedNode a bits tail) := NativeLayoutLoad.result_bound _ B hbegun
  have hready := loadedNode_ready s a bits tail hsource
  obtain ⟨ra,rd,rc,words,tboot,hw,htboot,hboot,hBboot⟩ := bootstrap_run s _ B hready hloaded hcap
    (loadedNode_empty a bits tail 710 (by decide))
    (loadedNode_empty a bits tail 711 (by decide))
    (loadedNode_empty a bits tail 712 (by decide))
  let c := bootstrapped s (loadedNode a bits tail) ra rd rc words
  have hc_frame (i : Fin 896) (hi : i ∈ framePorts) : c.stacks i=a.stacks i :=
    (bootstrapped_framePorts s _ ra rd rc words i hi).trans (loadedNode_frame a bits tail i hi)
  obtain ⟨tsetup,b,htsetup,hsetup,h832,h833,h834,h835,hscratch,hframe,hB⟩ :=
    PairNativeSetup.setupCaller_eval c H J B
      ((hc_frame 338 (by decide)).trans hmask) ((hc_frame 243 (by decide)).trans horder) hBboot
  have htime1 := QueryAssembler.Nodes.beginNodeCost_le a bits B hb hbits
  have htime2 := NativeLayoutLoad.cost_le (QueryAssembler.Nodes.begunNode a bits tail) B hbegun
  have he : Eval prepareNode
      (QueryAssembler.Nodes.beginNodeCost a bits+
        (NativeLayoutLoad.cost (QueryAssembler.Nodes.begunNode a bits tail)+(tboot+tsetup))) a b :=
    (QueryAssembler.Nodes.beginNode_eval a bits tail hcursor).seq
      ((NativeLayoutLoad.command_eval _).seq (hboot.seq hsetup))
  have ht : QueryAssembler.Nodes.beginNodeCost a bits+
      (NativeLayoutLoad.cost (QueryAssembler.Nodes.begunNode a bits tail)+(tboot+tsetup)) ≤         20000*(B+1)^4+300*(B+1) := by omega
  refine ⟨ra,rd,rc,words,
    QueryAssembler.Nodes.beginNodeCost a bits+
      (NativeLayoutLoad.cost (QueryAssembler.Nodes.begunNode a bits tail)+(tboot+tsetup)),b,hw,he,ht,hB,
    ready_after_setup s c b (bootstrapped_ready s _ hready ra rd rc words) hframe,
    h832,h833,h834,h835,?_,?_,hscratch,hframe,compiled_halt_trace he 301 832,?_⟩
  · rw [hframe 850 (by decide) (by decide) (by decide) (by decide) (by decide),
      bootstrapped_high s _ ra rd rc words 850 (by decide)]
    exact loadedNode_empty a bits tail 850 (by decide)
  · rw [hframe 851 (by decide) (by decide) (by decide) (by decide) (by decide),
      bootstrapped_high s _ ra rd rc words 851 (by decide)]
    exact loadedNode_empty a bits tail 851 (by decide)
  · have hin : dataBits (a.withPC (some (compiled prepareNode 301 832).entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro k z hk hz i
    have hx := StructuredSpace.local_stack_bound (compiled prepareNode 301 832)
      (steps:=20000*(B+1)^4+300*(B+1)+1) hin k z (by omega) hz i
    exact hx.trans (by omega)

/-- Every arithmetic word used by the authentic factor constructor is in the
proved frame of this actual prefix. -/
theorem arithmetic_mem_frame (i : Fin 768) (hi : i ∈ QueryReadyConstruction.arithmeticPorts) :
    i.castAdd 128 ∈ framePorts := by
  simp only [QueryReadyConstruction.arithmeticPorts,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

noncomputable def sourceSnapshot (a : Data) (bits : List Bool) (tail : List (List Bool)) :
    LeafHeadSetupProgram.Data :=
  projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort (loadedNode a bits tail)

theorem sourceSnapshot_ready (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool)) (h : NativeLayoutLoad.SourceBank s a) :
    Native.Ready s (sourceSnapshot a bits tail) := loadedNode_ready s a bits tail h

theorem sourceSnapshot_bound (a : Data) (bits : List Bool) (tail : List (List Bool)) (B : ℕ)
    (hc : a.stacks 301=Encoding.encodeList id (bits::tail)) (hb : WordBound B a) :
    WordBound B (sourceSnapshot a bits tail) := by
  have hencoded := hb 301
  rw [hc,Encoding.length_encodeList_cons] at hencoded
  have hbits : bits.length ≤ B := by simp only [id_eq] at hencoded; omega
  have htail : (Encoding.encodeList id tail).length ≤ B := by omega
  have hbegun := QueryAssembler.Nodes.begunNode_bound a bits tail B hb hbits htail
  exact fun i => NativeLayoutLoad.result_bound _ B hbegun (QueryAssembler.Nodes.lowPort i)

local notation "Hidden" => (fun i : Fin _ =>
  Fin.val i=320 ∨ Fin.val i=322 ∨ Fin.val i=770 ∨ Fin.val i=771 ∨ Fin.val i=781)

/-- Erasing opaque collector words gives a fresh local source cap. Port332
is deliberately visible here, so its actual high-mask length must be charged. -/
theorem sourceSnapshot_visible_bound (a : Data) (bits : List Bool)
    (tail : List (List Bool)) (A : ℕ)
    (hc : a.stacks 301=Encoding.encodeList id (bits::tail))
    (hb : ∀ i : Fin 768, ¬Hidden i → (a.stacks (i.castAdd 128)).length ≤ A) :
    ∀ i, ¬Hidden i → ((sourceSnapshot a bits tail).stacks i).length ≤ A := by
  have hencoded := hb 301 (by decide)
  change (a.stacks 301).length ≤ A at hencoded
  rw [hc,Encoding.length_encodeList_cons] at hencoded
  have hbits : bits.length ≤ A := by simp only [id_eq] at hencoded; omega
  have htail : (Encoding.encodeList id tail).length ≤ A := by omega
  have hbegun (i : Fin 896) (hlo : i.val<768) (hi : ¬Hidden i) :
      ((QueryAssembler.Nodes.begunNode a bits tail).stacks i).length ≤ A := by
    rw [QueryAssembler.Nodes.begunNode_stacks]
    split_ifs
    · exact htail
    · exact hbits
    · exact Nat.zero_le _
    · exact hb ⟨i.val,hlo⟩ hi
  have hloaded (i : Fin 896) (hlo : i.val<768) (hi : ¬Hidden i) :
      ((loadedNode a bits tail).stacks i).length ≤ A := by
    by_cases he : ∃ j : Fin 14,NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.low j)=i
    · obtain ⟨j,rfl⟩ := he
      rw [loadedNode,NativeLayoutLoad.result_low]
      apply hbegun
      · change 730+j.val<768
        have hj := j.isLt
        omega
      · change ¬(730+j.val=320 ∨ 730+j.val=322 ∨ 730+j.val=770 ∨
          730+j.val=771 ∨ 730+j.val=781)
        have hj := j.isLt
        omega
    by_cases hc' : i ∈ NativeLayoutLoad.clearPorts
    · rcases List.mem_append.mp hc' with hc'|hc'
      · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc'
        rcases hc' with rfl|rfl|rfl
        · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 684)).length ≤ A
          rw [NativeLayoutLoad.result_empty _ 684 (by decide)]
          exact Nat.zero_le _
        · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 660)).length ≤ A
          rw [NativeLayoutLoad.result_empty _ 660 (by decide)]
          exact Nat.zero_le _
        · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 665)).length ≤ A
          rw [NativeLayoutLoad.result_empty _ 665 (by decide)]
          exact Nat.zero_le _
      · obtain ⟨j,hj,hij⟩ := List.mem_map.mp hc'
        obtain ⟨k,_,hk⟩ := List.mem_map.mp hj
        exact False.elim (he ⟨k,hk ▸ hij⟩)
    · rw [loadedNode,NativeLayoutLoad.result_frame _ i hc']
      exact hbegun i hlo hi
  intro i hi
  exact hloaded (QueryAssembler.Nodes.lowPort i) i.isLt hi

/-- Repeating a node requires only the parked native inputs and the current
index to have the fresh source cap. Paid loading discards stale native scratch;
no bound on unrelated caller words is used here. -/
theorem sourceSnapshot_native_bound (a : Data) (bits : List Bool)
    (tail : List (List Bool)) (A : ℕ)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
    (hindex : (a.stacks 307).length ≤ A) :
    ∀ i : Fin 768, ((128 : ℕ) ≤ Fin.val i ∧ Fin.val i < 142) ∨ i=307 ∨ i=660 ∨ i=665 →
      ((sourceSnapshot a bits tail).stacks i).length ≤ A := by
  have hlow (j : Fin 14) :
      ((sourceSnapshot a bits tail).stacks (LayoutMasters.low j)).length ≤ A := by
    change ((NativeLayoutLoad.result (QueryAssembler.Nodes.begunNode a bits tail)).stacks
      (NativeLayoutLoad.stackMap (LayoutMasters.low j))).length ≤ A
    rw [NativeLayoutLoad.result_low]
    have hf : NativeLayoutLoad.stackMap (LayoutMasters.high j) ∉         301::QueryAssembler.Nodes.nodeResetPorts := by
      simp only [QueryAssembler.Nodes.nodeResetPorts,List.mem_cons,
        List.not_mem_nil,or_false]
      intro h
      rcases h with h|h|h|h|h|h|h|h|h|h
      all_goals have hv := congrArg Fin.val h
      all_goals change 730+j.val=_ at hv
      all_goals simp only [Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hv
      all_goals have hj := j.isLt
      all_goals omega
    rw [QueryAssembler.Nodes.begunNode_frame a bits tail _ hf]
    exact hparked j
  intro i hi
  rcases hi with hi|rfl|rfl|rfl
  · let j : Fin 14 := ⟨i.val-128,by omega⟩
    have hj : LayoutMasters.low j=i := by apply Fin.ext; change 128+(i.val-128)=i.val; omega
    rw [←hj]
    exact hlow j
  · exact (congrArg List.length (loadedNode_frame a bits tail 307 (by decide))).le.trans hindex
  · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 660)).length ≤ A
    rw [NativeLayoutLoad.result_empty _ 660 (by decide)]
    exact Nat.zero_le _
  · change ((NativeLayoutLoad.result _).stacks (NativeLayoutLoad.stackMap 665)).length ≤ A
    rw [NativeLayoutLoad.result_empty _ 665 (by decide)]
    exact Nat.zero_le _

/-- The genuine restricted source constructor receives bounds on exactly
its sixteen retained native words, even after arbitrarily large local scratch. -/
theorem sourceSnapshot_retained_bound (a : Data) (bits : List Bool)
    (tail : List (List Bool)) (A : ℕ)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
    (hindex : (a.stacks 307).length ≤ A) :
    ∀ i ∈ QuerySourceSnapshot.retainedPorts,
      ((sourceSnapshot a bits tail).stacks i).length ≤ A := by
  intro i hi
  apply sourceSnapshot_native_bound a bits tail A hparked hindex i
  simp only [QuerySourceSnapshot.retainedPorts,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

def cacheInputPorts : List (Fin 896) :=
  [194,201,202,203,204,207,211,212,243,280,281,730]

/-- The cache-copy bound follows the actual visible ring masters. It stays
independent of larger retained tuple and collector words. -/
theorem prepared_common_cache_bound {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool} {P A : ℕ}
    {a b : Data} (h : QueryReadyConstruction.CommonReady q node H high P b)
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hambient : a.stacks 730=List.replicate n true)
    (hvisible : ∀ i ∈ cacheInputPorts,(a.stacks i).length ≤ A) :
    QueryReadyConstruction.CommonReady q node H high A b := by
  have h128 : (b.stacks 128).length ≤ A := by
    have hn := hvisible 730 (by decide)
    change (a.stacks 730).length ≤ A at hn
    rw [hambient,List.length_replicate] at hn
    simpa only [h.ambient,List.length_replicate] using hn
  have hword (i : Fin 768) (hi : i.castAdd 128 ∈ framePorts)
      (hv : i.castAdd 128 ∈ cacheInputPorts) :
      (b.stacks (i.castAdd 128)).length ≤ A := by
    rw [hframe _ hi]
    exact hvisible (i.castAdd 128) hv
  refine {h with
    cacheCaps := ?_
    ambientCap := h128
    oneCap := hword 207 (by decide) (by decide)}
  intro p hp
  simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
    List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact h128 | exact hword _ (by decide) (by decide)

/-- The actual native cache witness is coupled to its source snapshot and
current head masters, with the real starting address on649. -/
theorem prepared_source (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (b : Data)
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) :
    SignatureHeadLoader.MasterFrame (Native.start s (sourceSnapshot a bits tail) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) ∧
      b.stacks 649=unary (s.node.val*s.r) := by
  constructor
  · constructor
    intro i hi
    have hn : QueryAssembler.Nodes.lowPort i ∉ PairNativeSetup.scratch ∧
        QueryAssembler.Nodes.lowPort i ≠ 832 ∧ QueryAssembler.Nodes.lowPort i ≠ 833 ∧
        QueryAssembler.Nodes.lowPort i ≠ 834 ∧ QueryAssembler.Nodes.lowPort i ≠ 835 := by
      simp only [SignatureHeadLoader.masters,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    exact (hf _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((bootstrapped_low s _ ra rd rc words i).trans
        ((SignatureHeadLoader.bootstrapResult_masters s _ ra rd rc words).stored i hi))
  · rw [hf 649 (by decide) (by decide) (by decide) (by decide) (by decide)]
    have hlow := bootstrapped_low s (loadedNode a bits tail) ra rd rc words 649
    change (bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks
      (QueryAssembler.Nodes.lowPort 649)=_
    rw [hlow,SignatureHeadLoader.bootstrapResult,
      retainedState_frame _ 649 (by decide) (by decide) (by decide) (by decide)]
    exact bootState_address _ ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

/-- The concrete node prefix constructs its authentic query specification
from the actual arithmetic output and its freshly produced cache witness.
Neither pair mask is assumed on entry; both accumulators are physically empty. -/
theorem prepare_native_run
    (s : Native.Inputs) (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (hQ : m.val 21=s.Q)
    (hR : (base.stacks 740).length=s.R) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (H : Finset (Fin s.n)) (high : H → Bool) (B : ℕ) (a : Data)
    (hbank : NativeLayoutLoad.SourceBank s a)
    (tail : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id
      (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))::tail))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i ∈ QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h700 : a.stacks 700=Encoding.encodeList id q.clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (h704 : a.stacks 704=List.replicate q.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex q))
    (h706 : a.stacks 706=[q.mark.isSome])
    (h707 : a.stacks 707=q.modulus) (h708 : a.stacks 708=q.width)
    (h702 : a.stacks 702=List.ofFn (fun v : Fin s.n => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn (fun v : Fin s.n => if h:v ∈ H then high ⟨v,h⟩ else false))
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
    ∃ (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)),
    ∃ hw : CacheCorrect s.height (unary s.R) s.width words, ∃ ticks b,
      let snap := sourceSnapshot a
        (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))) tail
      let spec := nativeSpecOfInputs s m ht hd words hw M cache half e ho.produced
        hfield q hv (m.val 42) hJ source hsource
      Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
      WordBound B b ∧ QueryReadyConstruction.CommonReady spec s.node H high B b ∧
      QueryPairCommit.NodeAccumulatorMeaning spec 0 b ∧ PairAccumulatorMeaning spec 0 b ∧
      b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate spec.J true ∧
      b.stacks 834=[] ∧ b.stacks 835=[] ∧
      b.stacks 301=Encoding.encodeList id tail ∧ b.stacks 307=a.stacks 307 ∧
      b.stacks 863=a.stacks 863 ∧ (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
      Native.Ready s snap ∧ WordBound B snap ∧
      SignatureHeadLoader.MasterFrame (Native.start s snap ra rd rc words)
        (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) ∧
      b.stacks 649=unary (s.node.val*s.r) ∧
      Trace (compiled prepareNode 301 832) (ticks+1)
        (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
      ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
        (a.withPC (some (compiled prepareNode 301 832).entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1 := by
  have horder : a.stacks 243=List.replicate (m.val 42) true :=
    (hframe 243 (by decide)).trans ((ho.low 243 (by decide)).trans ho.produced.jetOrder)
  obtain ⟨ra,rd,rc,words,ticks,b,hw,he,htime,hB,hnative,h832,h833,h834,h835,h850,h851,
      _hscratch,hf,htrace,hprefix⟩ :=
    prepare_eval s a _ tail H (m.val 42) B hbank hcursor hmask horder hb hcap
  obtain ⟨htheta,hcursor',hframe',hpositive,hnegative,hpower⟩ :=
    prepared_words s a _ tail ra rd rc words b hf
  have harith (i : Fin 768) (hi : i ∈ QueryReadyConstruction.arithmeticPorts) :
      b.stacks (i.castAdd 128)=out.stacks i :=
    (hframe' _ (arithmetic_mem_frame i hi)).trans (hframe i hi)
  have hcommon := QueryReadyConstruction.native_common s m ht hd words hw M cache half e
    base out ho hfield hQ hR q hv hJ source hsource H high B b hnative harith hdegree htheta
    hpositive hnegative hpower
    ((hframe' 700 (by decide)).trans h700) ((hframe' 701 (by decide)).trans h701)
    ((hframe' 704 (by decide)).trans h704) ((hframe' 705 (by decide)).trans h705)
    ((hframe' 706 (by decide)).trans h706) ((hframe' 707 (by decide)).trans h707)
    ((hframe' 708 (by decide)).trans h708) ((hframe' 702 (by decide)).trans h702)
    ((hframe' 703 (by decide)).trans h703) (fun i _ => hB i)
  obtain ⟨hmasters,haddress⟩ := prepared_source s a _ tail ra rd rc words b hf
  refine ⟨ra,rd,rc,words,hw,ticks,b,he,htime,hB,hcommon,
    QueryPairCommit.NodeAccumulatorMeaning.zero _ b h850,
    PairAccumulatorMeaning.zero _ b h851,h832,h833,h834,h835,hcursor',
    hframe' 307 (by decide),hframe' 863 (by decide),hframe',
    sourceSnapshot_ready s a _ tail hbank,sourceSnapshot_bound a _ tail B hcursor hb,
    hmasters,haddress,htrace,hprefix⟩

/-- Reassociating the proved concrete prefix with the fixed pair and finish
commands preserves its exact execution, rather than selecting another run. -/
theorem nodeBody_eval {np nq nf : ℕ} {a b c d : Data}
    (hp : Eval prepareNode np a b) (hq : Eval QueryStreamProgram.pairs nq b c)
    (hf : Eval QueryNodeFinish.command nf c d) :
    Eval QueryStreamProgram.nodeBody (np+nq+nf) a d := by
  cases hp with
  | seq hbegin hrest =>
    cases hrest with
    | seq hload hrest =>
      cases hrest with
      | seq hboot hsetup =>
        simpa only [QueryStreamProgram.nodeBody,Nat.add_assoc] using
          hbegin.seq (hload.seq (hboot.seq (hsetup.seq (hq.seq hf))))

/-- The polynomial preparation and readout budgets enter the transient cap;
the potentially exponential pair time does not. All three traces are the
actual segments of the same fixed node-body execution. -/
theorem nodeBody_prefix {np nq nf B D : ℕ} {a b c d : Data}
    (hp : Eval prepareNode np a b) (hq : Eval QueryStreamProgram.pairs nq b c)
    (hf : Eval QueryNodeFinish.command nf c d)
    (ha : WordBound B a) (hc : WordBound B c)
    (hspace : QueryExecution.PrefixBound QueryStreamProgram.pairs nq b D) :
    QueryExecution.PrefixBound QueryStreamProgram.nodeBody (np+nq+nf+1) a
      (max D (896*B+np+nf+1)) := by
  have hmass : stackBits a.stacks ≤ 896*B :=
    StreamResources.dataBits_le_mul (a.withPC (none : Option (Fin 1))) ha
  have growth {command : Code} {n : ℕ} {u v : Data} (he : Eval command n u v) :
      stackBits v.stacks ≤ stackBits u.stacks+n := by
    have htrace := compiled_trace (c:=command) (a:=u) (b:=v) he 838 838
    have hg := trace_dataBits (compiled command 838 838) htrace
    exact hg
  have localPrefix {command : Code} {n spent : ℕ} {u : Data}
      (hm : stackBits u.stacks ≤ 896*B+spent) (hn : spent+n ≤ np+nf+1) :
      QueryExecution.PrefixBound command n u (max D (896*B+np+nf+1)) := by
    constructor
    intro elapsed z ht hz i
    have hin : dataBits (u.withPC (some (compiled command 838 838).entry)) ≤ 896*B+spent := hm
    have hx := StructuredSpace.local_stack_bound (compiled command 838 838)
      (a:=u.withPC (some (compiled command 838 838).entry))
      (steps:=n) (initialBound:=896*B+spent) hin elapsed z ht hz i
    exact hx.trans ((by omega : 896*B+spent+n ≤ 896*B+np+nf+1).trans (Nat.le_max_right _ _))
  cases hp with
  | @seq _ _ n0 nr0 _ a1 _ h0 hr0 =>
    cases hr0 with
    | @seq _ _ n1 nr1 _ a2 _ h1 hr1 =>
      cases hr1 with
      | @seq _ _ n2 n3 _ a3 _ h2 h3 =>
        have hb1 := growth h0
        have hb2 := growth (h0.seq h1)
        have hb3 := growth (h0.seq (h1.seq h2))
        have p0 := localPrefix (command:=QueryAssembler.Nodes.beginNode) (n:=n0) (spent:=0) (u:=a)
          (by omega) (by omega)
        have p1 := localPrefix (command:=NativeLayoutLoad.command) (n:=n1) (spent:=n0) (u:=a1)
          (by omega) (by omega)
        have p2 := localPrefix (command:=QueryStreamProgram.bootstrapNode) (n:=n2) (spent:=n0+n1) (u:=a2)
          (by omega) (by omega)
        have p3 := localPrefix (command:=PairNativeSetup.setupCaller) (n:=n3) (spent:=n0+n1+n2) (u:=a3)
          (by omega) (by omega)
        have hend : stackBits c.stacks ≤ 896*B :=
          StreamResources.dataBits_le_mul (c.withPC (none : Option (Fin 1))) hc
        have pf := localPrefix (command:=QueryNodeFinish.command) (n:=nf) (spent:=0) (u:=c)
          (by omega) (by omega)
        have pq := hspace.mono (Nat.le_max_left D (896*B+(n0+(n1+(n2+n3)))+nf+1))
        have hprefix := QueryExecution.prefix_seq h0 (h1.seq (h2.seq (h3.seq (hq.seq hf)))) p0
          (QueryExecution.prefix_seq h1 (h2.seq (h3.seq (hq.seq hf))) p1
            (QueryExecution.prefix_seq h2 (h3.seq (hq.seq hf)) p2
              (QueryExecution.prefix_seq h3 (hq.seq hf) p3 (QueryExecution.prefix_seq hq hf pq pf))))
        have he := nodeBody_eval (h0.seq (h1.seq (h2.seq h3))) hq hf
        constructor
        apply StructuredSpace.compiled_halt_stack_bound he 838 838
        simpa only [QueryStreamProgram.nodeBody,Nat.add_assoc] using hprefix.bound

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

/-- Every static node word also has an exact frame through the actual pair loop. -/
theorem framePorts_pair (i : Fin 896) (hi : i ∈ framePorts) :
    i ∈ QueryPairEvaluation.framePorts := by
  simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Readout changes the node index and coefficient stream, preserving the
complete static context used by the next node and final reconstruction. -/
theorem framePorts_finish (i : Fin 896) (hi : i ∈ framePorts) (h307 : i ≠ 307) (h863 : i ≠ 863) :
    i ∉ QueryNodeFinish.touchedPorts := by
  simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact False.elim (h307 rfl) | exact False.elim (h863 rfl) | decide

/-- Complete the very node prefix already executed by `prepare_native_run`.
The pair traversal, tuple evaluator and coefficient readout are the fixed
proved programs. Their retained endpoint cap is shared, and pair running time
never becomes a space estimate. The signed value is subsequently identified
with the shifted source target by the actual source-data lemmas. -/
theorem finish_prepared_node (s : SignatureTupleSource.ProducedSource)
    {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (a b : Data) (np index : ℕ) (remaining : List (List Bool))
    (hp : Eval prepareNode np a b)
    (ha : WordBound F a) (hb : WordBound F b)
    (hcommon : QueryReadyConstruction.CommonReady q s.input.node H high M b)
    (hzero : QueryPairCommit.NodeAccumulatorMeaning q 0 b)
    (hmasters : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b))
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hmask : b.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : b.stacks 649=unary s.base)
    (hdepth : b.stacks 832=List.replicate (s.input.n-H.card) true)
    (hbudget : b.stacks 833=List.replicate q.J true)
    (houter : b.stacks 834=[]) (hinner : b.stacks 835=[])
    (hcursor : b.stacks 301=Encoding.encodeList id remaining)
    (hindex : b.stacks 307=List.replicate index true)
    (hout : (b.stacks 863).length+q.J*(d*baseWidth 3 q.p.t) ≤ F)
    (hnext : index+1 ≤ F) :
    ∃ steps e, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
      Eval QueryStreamProgram.nodeBody steps a e ∧
      codes.length=q.J ∧
      codes.map q.p.ops.decode=List.ofFn
        (∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
          (-1)^(pair.1.card-pair.2.card)*
            QueryPairEvaluation.pairValue s q H high owner head facts pair.1 pair.2).coeff ∧
      e.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      e.stacks 301=Encoding.encodeList id remaining ∧
      e.stacks 307=List.replicate (index+1) true ∧
      e.regs 37= !remaining.isEmpty ∧ e.regs 38=true ∧ e.stacks 89=[] ∧
      (∀ i ∈ framePorts,i ≠ 307 → i ≠ 863 → e.stacks i=a.stacks i) ∧
      WordBound F e ∧
      steps ≤ np+DifferencePairsProgram.cost
        (QueryPairEvaluation.callbackBudget s q (s.input.n-H.card) F S Z B height)
        (s.input.n-H.card) q.J+
        QueryNodeFinish.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F ∧
      Trace (compiled QueryStreamProgram.nodeBody 838 838) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.nodeBody 838 838).entry)) (e.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (max (max (QueryPairEvaluation.callbackSpace s q (s.input.n-H.card) F B) (896*F+13))
          (896*F+np+QueryNodeFinish.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+1)) := by
  have hi : QueryPairEvaluation.Invariant q s.input.node H high M F s b 0 b :=
    ⟨hcommon,hzero,fun i _=>hb i,hmasters,fun _ _=>rfl⟩
  obtain ⟨nq,c,hq,_htrace,hI,_hcontrols,hc,hqt,hqp⟩ :=
    QueryPairEvaluation.run s q H high owner head facts caps cap hheads b 0 hi
      hmask haddress hb hdepth hbudget houter hinner
  have h301 : c.stacks 301=Encoding.encodeList id remaining :=
    (hI.frame 301 (by decide)).trans hcursor
  have h307 : c.stacks 307=List.replicate index true :=
    (hI.frame 307 (by decide)).trans hindex
  have h863 : c.stacks 863=b.stacks 863 := hI.frame 863 (by decide)
  have hcOut : (c.stacks 863).length+q.J*(d*baseWidth 3 q.p.t) ≤ F := by
    rw [h863]
    exact hout
  obtain ⟨nf,e,codes,hf,hlen,hvalue,hout',_h78,_h850,_h862,hscratch,hindex',hguard,hpeek,
    hfframe,hebound,hft,_hftrace,_hfspace⟩ :=
    QueryNodeReadout.run_common q s.input.node H high M F index c hI.common _ hI.accumulator
      remaining h301 h307 hc hcOut hnext
  have hall := nodeBody_eval hp hq hf
  have hpairs : QueryExecution.PrefixBound QueryStreamProgram.pairs nq b
      (max (QueryPairEvaluation.callbackSpace s q (s.input.n-H.card) F B) (896*F+13)) :=
    ⟨fun elapsed cfg ht hz i => hqp elapsed cfg (by omega) hz i⟩
  have hpref := nodeBody_prefix hp hq hf ha hc hpairs
  refine ⟨np+nq+nf,e,codes,hall,hlen,?_,?_,?_,hindex',hguard,hpeek,
    hscratch 89 (by decide),?_,hebound,?_,compiled_halt_trace hall 838 838,?_⟩
  · simpa only [zero_add] using hvalue
  · rw [hout',h863,hframe 863 (by decide)]
  · exact (hfframe 301 (by decide)).trans h301
  · intro i him h307' h863'
    exact (hfframe i (framePorts_finish i him h307' h863')).trans
      ((hI.frame i (framePorts_pair i him)).trans (hframe i him))
  · omega
  · apply hpref.mono
    exact max_le_max (Nat.le_refl _) (by omega)


/-- The source bank already pays for the current index: its unary node count
bounds the actual unary index. No independent per-node cap is assumed. -/
theorem sourceSnapshot_bank_bound (s : Native.Inputs) (a : Data)
    (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
    (hbank : NativeLayoutLoad.SourceBank s a)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A) :
    ∀ i ∈ QuerySourceSnapshot.retainedPorts,
      ((sourceSnapshot a bits remaining).stacks i).length ≤ A := by
  apply sourceSnapshot_retained_bound a bits remaining A hparked
  have hQ := hparked 3
  change (a.stacks 733).length ≤ A at hQ
  rw [hbank.nodes,unary,List.length_replicate] at hQ
  rw [hbank.node,unary,List.length_replicate]
  exact s.node.isLt.le.trans hQ

section AddressedSource
variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)

/-- The source used by the concrete tuple run is built from this actual
node's loaded input and this actual bootstrap's cache witnesses. Its fresh cap
uses only parked input words; the running state is never replaced or cleared. -/
noncomputable def nodeSource : SignatureTupleSource.ProducedSource :=
  QueryHeadSourceFacts.addressedSource query k hg first tail node
    (QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining))
    (QuerySourceSnapshot.snapshot_ready (sourceSnapshot_ready native a bits remaining hbank))
    A (QuerySourceSnapshot.snapshot_bound _ A
      (sourceSnapshot_bank_bound native a bits remaining A hbank hparked))
    ra rd rc words hc

local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

/-- All native source data, including the exact register and cache witnesses,
remain attached to the actual addressed node; the source cap is exactly A. -/
theorem nodeSource_data :
    (src).input=native ∧ (src).bound=A ∧ (src).cacheWords=words := ⟨rfl,rfl,rfl⟩

/-- Only the eighteen-master reference changes to the restricted source.
The physical caller and its full query frame stay exactly the actual states. -/
theorem nodeSource_masters (b : Data)
    (hm : SignatureHeadLoader.MasterFrame
      (Native.start native (sourceSnapshot a bits remaining) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b)) :
    SignatureHeadLoader.MasterFrame (src).masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  exact (hm.stored i hi).trans
    ((QuerySourceSnapshot.snapshot_masters native (sourceSnapshot a bits remaining)
      ra rd rc words).stored i hi).symm

/-- The authentic source semantic facts are derived for this same bounded
snapshot; no independently supplied source, owner or selected head is used. -/
theorem nodeSource_facts
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (native).Q < 3^(m.val 34)) (hv : query.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (native).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source) :
    QueryVisitorHead.SourceFacts (src).input
      (QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
        hfield query hv hJ source hsource)
      (HighMarkedFrontend.highSet query)
      ((ProducedQueryRank.owner (LeafProgram.Query.packingProblem query k hg)) ∘
        Fin.cast (Native.Inputs.plans_length native)) (src).owner
      (fun t v => ProducedQueryRank.words (LeafProgram.Query.packingProblem query k hg)
        first tail (Sum.inl v) t) :=
  QueryHeadSourceFacts.sourceFacts query k hg first tail node
    (QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining))
    (QuerySourceSnapshot.snapshot_ready (sourceSnapshot_ready native a bits remaining hbank))
    A (QuerySourceSnapshot.snapshot_bound _ A
      (sourceSnapshot_bank_bound native a bits remaining A hbank hparked))
    ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource

section FactorRun
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (produced : LeafRingSetupProgram.Produced m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34)) (hv : query.Valid) (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e produced
  hfield query hv hJ source hsource
local notation "H" => HighMarkedFrontend.highSet query
local notation "sourceOwner" => ProducedQueryRank.owner (LeafProgram.Query.packingProblem query k hg) ∘
  Fin.cast (Native.Inputs.plans_length native)
local notation "sourceHead" => (fun t v => ProducedQueryRank.words
  (LeafProgram.Query.packingProblem query k hg) first tail (Sum.inl v) t)
local notation "sourceFacts" => nodeSource_facts query k hg first tail node a bits remaining A
  hbank hparked ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource

include hfield source hsource in
/-- The very addressed source and cache produced for this node instantiate
all source-target correspondence conditions of the completed pair run. -/
theorem nodeSource_target (high : H → Bool) :
    (∑ pair ∈ BooleanDifferences.pairFamily ((native).n-(H).card) (spec).J,
      (-1)^(pair.1.card-pair.2.card)*
        QueryPairEvaluation.pairValue src spec H high sourceOwner sourceHead sourceFacts
          pair.1 pair.2) =
      Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
        (Polynomial.X+Polynomial.C ((spec).p.ops.decode (spec).theta))) :=
  QueryAddressedTarget.signed_pair_target query k hg first tail node
    (QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining))
    (QuerySourceSnapshot.snapshot_ready (sourceSnapshot_ready native a bits remaining hbank))
    A (QuerySourceSnapshot.snapshot_bound _ A
      (sourceSnapshot_bank_bound native a bits remaining A hbank hparked))
    ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource high


include hfield source hsource in
/-- Finish the actual native node with its own bounded source and cache.
All semantic source alignment is instantiated here; the numerical data bounds
are supplied by the separate concrete source-bound construction. -/
theorem nodeSource_run (high : H → Bool) (F S Z T width height : ℕ)
    (caps : QueryVisitorHead.HeadBounds (src).input spec A F S Z T A width)
    (cap : SignatureTupleComplete.RetainedCap src F)
    (hheads : ∀ depth<(native).r,(src).headSize depth ≤ height)
    (b : Data) (np : ℕ) (hp : Eval prepareNode np a b)
    (ha : WordBound F a) (hb : WordBound F b)
    (hcommon : QueryReadyConstruction.CommonReady spec node H high A b)
    (hzero : QueryPairCommit.NodeAccumulatorMeaning spec 0 b)
    (hmasters : SignatureHeadLoader.MasterFrame
      (Native.start native (sourceSnapshot a bits remaining) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b))
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hmask : b.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : b.stacks 649=unary (src).base)
    (hdepth : b.stacks 832=List.replicate ((native).n-(H).card) true)
    (hbudget : b.stacks 833=List.replicate (spec).J true)
    (houter : b.stacks 834=[]) (hinner : b.stacks 835=[])
    (hcursor : b.stacks 301=Encoding.encodeList id remaining)
    (hout : (b.stacks 863).length+(spec).J*((m.val 34)*baseWidth 3 (spec).p.t) ≤ F)
    (hnext : node.val+1 ≤ F) :
    ∃ steps z, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 (spec).p.t)) (m.val 34)),
      Eval QueryStreamProgram.nodeBody steps a z ∧
      codes.length=(spec).J ∧
      codes.map (spec).p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
          (Polynomial.X+Polynomial.C ((spec).p.ops.decode (spec).theta)))).coeff ∧
      z.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      z.stacks 301=Encoding.encodeList id remaining ∧
      z.stacks 307=List.replicate (node.val+1) true ∧
      z.regs 37= !remaining.isEmpty ∧ z.regs 38=true ∧ z.stacks 89=[] ∧
      (∀ i ∈ framePorts,i ≠ 307 → i ≠ 863 → z.stacks i=a.stacks i) ∧
      WordBound F z ∧
      steps ≤ np+DifferencePairsProgram.cost
        (QueryPairEvaluation.callbackBudget src spec ((native).n-(H).card) F S Z T height)
        ((native).n-(H).card) (spec).J+
        QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t) (m.val 34) (spec).p.t (spec).J F ∧
      Trace (compiled QueryStreamProgram.nodeBody 838 838) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.nodeBody 838 838).entry)) (z.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (max (max (QueryPairEvaluation.callbackSpace src spec ((native).n-(H).card) F T) (896*F+13))
          (896*F+np+QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t)
            (m.val 34) (spec).p.t (spec).J F+1)) := by
  have hm := nodeSource_masters query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc b hmasters
  have hi : b.stacks 307=List.replicate node.val true :=
    (hframe 307 (by decide)).trans hbank.node
  have hr := finish_prepared_node src spec H high sourceOwner sourceHead sourceFacts caps cap
    hheads a b np node.val remaining hp ha hb hcommon hzero hm hframe hmask haddress
    hdepth hbudget houter hinner hcursor hi hout hnext
  have htarget := nodeSource_target query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource high
  obtain ⟨steps,z,codes,he,hlen,hcodes,hrest⟩ := hr
  exact ⟨steps,z,codes,he,hlen,hcodes.trans
    (congrArg (fun value : Truncated ((spec).p.model.O (spec).p.t) (spec).J =>
      List.ofFn value.coeff) htarget),hrest⟩

end FactorRun

end AddressedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
