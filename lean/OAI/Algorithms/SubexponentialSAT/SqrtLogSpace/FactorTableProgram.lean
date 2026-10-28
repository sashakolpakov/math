import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLiteral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyTable
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryIncidenceCommand

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem not_mem_union {α : Type*} [DecidableEq α]
    {a : α} {s t : Finset α} (hs : a ∉ s) (ht : a ∉ t) : a ∉ s ∪ t := by
  simpa only [Finset.mem_union, not_or] using And.intro hs ht

abbrev OuterCode := Cmd 16 896
abbrev OuterStore := Fin 896 → List Bool
abbrev OuterData := State 16 896

def innerPort (i : Fin 256) : Fin 896 := ⟨340+i.val, by omega⟩
theorem innerPort_injective : Function.Injective innerPort := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [innerPort] at this
  omega

def liftInner (code : Cmd 16 256) : OuterCode :=
  liftCommand code 0 0 id innerPort

def basePort (i : Fin 768) : Fin 896 :=
  if i = 640 then 885 else if i = 641 then 886 else
  if i = 642 then 887 else if i = 647 then 888 else
  if i = 650 then 889 else if i = 651 then 890 else
  if i = 670 then 891 else if i = 671 then 892 else i.castAdd 128

private def decodeBasePort (i : Fin 896) : ℕ :=
  if i = 885 then 640 else if i = 886 then 641 else
  if i = 887 then 642 else if i = 888 then 647 else
  if i = 889 then 650 else if i = 890 then 651 else
  if i = 891 then 670 else if i = 892 then 671 else i.val

private theorem decodeBasePort_low (i : Fin 896) (hi : i.val < 768) :
    decodeBasePort i = i.val := by
  have h885 : i ≠ 885 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h886 : i ≠ 886 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h887 : i ≠ 887 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h888 : i ≠ 888 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h889 : i ≠ 889 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h890 : i ≠ 890 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h891 : i ≠ 891 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h892 : i ≠ 892 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp only [decodeBasePort, ite_eq_right h885, ite_eq_right h886, ite_eq_right h887,
    ite_eq_right h888, ite_eq_right h889, ite_eq_right h890, ite_eq_right h891,
    ite_eq_right h892]

private theorem decodeBasePort_basePort (i : Fin 768) : decodeBasePort (basePort i) = i.val := by
  unfold basePort
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · exact decodeBasePort_low _ i.isLt

theorem basePort_injective : Function.Injective basePort := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg decodeBasePort hij
  simpa only [decodeBasePort_basePort] using hv

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

/-- These are live caller words, never source scratch after relocation. -/
def protectedPorts : List (Fin 896) := [640,641,642,647,650,651,670,671]

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

/-- The source, staging and cleanup instruction tables all use this same
embedding. Its protected caller words survive every source instruction. -/
theorem base_prefix_frame {l steps prefixSteps : ℕ}
    (p : Program 16 768 l) (frame : Cfg 16 896 l) {a b : Cfg 16 768 l}
    (tr : Trace p steps a b) {intermediate : Cfg 16 896 l}
    (hp : prefixSteps ≤ steps)
    (ht : Trace (ProgramLinking.liftProgram p id basePort) prefixSteps
      (ProgramLinking.embedCfg id basePort id none frame a) intermediate)
    (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    intermediate.stacks i = frame.stacks i :=
  StreamResources.relocate_trace_stack_frame p _ id basePort id none frame
    Function.injective_id basePort_injective (fun _ => rfl) tr hp ht i
    (basePort_outside i hi)

theorem basePort_low (i : Fin 768) (hi : i.val < 640) : basePort i = i.castAdd 128 := by
  have hn (j : Fin 768) (hj : 640 ≤ j.val) : i ≠ j := by
    intro h
    subst j
    omega
  simp only [basePort, ite_eq_right (hn 640 (by decide)),
    ite_eq_right (hn 641 (by decide)), ite_eq_right (hn 642 (by decide)),
    ite_eq_right (hn 647 (by decide)), ite_eq_right (hn 650 (by decide)),
    ite_eq_right (hn 651 (by decide)), ite_eq_right (hn 670 (by decide)),
    ite_eq_right (hn 671 (by decide))]

theorem basePort_inner (i : Fin 256) :
    basePort (PerturbationAssembly.innerPort i) = innerPort i := by
  rw [basePort_low _ (by change 340+i.val<640; omega)]
  rfl

def liftBase (code : Cmd 16 768) : OuterCode :=
  liftCommand code 0 0 id basePort

def joinedPort (i : Fin 294) : Fin 896 := ⟨340+i.val, by omega⟩

theorem joinedPort_injective : Function.Injective joinedPort := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [joinedPort] at this
  omega

theorem emptyHigh_update (mask : List Bool) :
    QueryProducerSpace.Native.emptyHigh mask =
      Function.update (QueryProducerSpace.Native.emptyHigh []) 29 mask := by
  funext i
  fin_cases i <;> rfl

theorem joinedState_update_mask (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) :
    (QueryProducerSpace.Native.joinedState regs low
      (QueryProducerSpace.Native.emptyHigh mask)).stacks =
      Function.update (QueryProducerSpace.Native.joinedState regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks 285 mask := by
  funext i
  refine Fin.addCases (m := 256) (n := 38) (fun j => ?_) (fun j => ?_) i
  · have hn : (j.castAdd 38 : Fin 294) ≠ 285 := by
      intro h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      simp only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
      omega
    simp [QueryProducerSpace.Native.joinedState, hn]
  · rw [emptyHigh_update]
    by_cases hj : j = 29
    · subst j
      change (QueryProducerSpace.Native.joinedState regs low
        (Function.update (QueryProducerSpace.Native.emptyHigh []) 29 mask)).stacks
        (QueryProducerSpace.Native.producerPorts 29) = mask
      rw [QueryProducerSpace.Native.joinedState_high, Function.update_self]
    · have hn : (Fin.natAdd 256 j : Fin 294) ≠ 285 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
        apply hj
        apply Fin.ext
        simp only [Fin.coe_ofNat_eq_mod]
        omega
      simp [QueryProducerSpace.Native.joinedState, hj, hn]

theorem copied_joined_shape (a : OuterData) (low : Fin 256 → List Bool)
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    projectState id joinedPort (SubexpSetupStorage.copyState 857 625 a) =
      QueryProducerSpace.Native.joinedState
        (SubexpSetupStorage.copyState 857 625 a).regs low
        (QueryProducerSpace.Native.emptyHigh (a.stacks 857)) := by
  apply state_ext
  · rfl
  · rw [joinedState_update_mask]
    funext i
    by_cases hi : i = 285
    · subst i
      have hz : a.stacks 625 = [] := hs 285
      simp [projectState, SubexpSetupStorage.copyState, StackRoutines.copyStacks, joinedPort, Fin.coe_ofNat_eq_mod, hz]
    · have hn : joinedPort i ≠ 625 := by
        intro h
        apply hi
        apply joinedPort_injective
        exact h
      simp only [projectState, SubexpSetupStorage.copyState, StackRoutines.copyStacks,
        Function.comp_apply, Function.update_of_ne hn, Function.update_of_ne hi]
      exact hs i

theorem joinedState_update_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) (word : List Bool) :
    (QueryProducerSpace.Native.joinedState regs (Function.update low 217 word) high).stacks =
      Function.update (QueryProducerSpace.Native.joinedState regs low high).stacks 217 word := by
  funext i
  refine Fin.addCases (m := 256) (n := 38) (fun j => ?_) (fun j => ?_) i
  · by_cases hj : j = 217
    · subst j; rfl
    · have hn : (j.castAdd 38 : Fin 294) ≠ 217 := by
        intro h
        apply hj
        have hv := congrArg (fun x : Fin 294 => x.val) h
        exact Fin.ext hv
      simp [QueryProducerSpace.Native.joinedState, hj, hn]
  · have hn : (Fin.natAdd 256 j : Fin 294) ≠ 217 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
      omega
    simp [QueryProducerSpace.Native.joinedState, hn]

/-- The producer reclaims its copied mask and all high scratch. Exactly its
specialized low output replaces caller557; every other caller word returns. -/
theorem specialized_joined_output (a : OuterData) (low : Fin 256 → List Bool)
    (rr : Fin 16 → Bool) (word : List Bool)
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    embedState id joinedPort (SubexpSetupStorage.copyState 857 625 a)
      (QueryProducerSpace.Native.joinedState rr (Function.update low 217 word)
        (QueryProducerSpace.Native.emptyHigh [])) =
      (⟨rr, Function.update a.stacks 557 word⟩ : OuterData) := by
  apply embedState_eq_of_ports id joinedPort _ _ _ Function.injective_id joinedPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    change Function.update a.stacks 557 word (joinedPort i) = _
    rw [joinedState_update_low]
    by_cases hi : i = 217
    · subst i; rfl
    · have hn : joinedPort i ≠ 557 := by
        intro h
        apply hi
        apply joinedPort_injective
        exact h
      simp only [Function.update_of_ne hn, Function.update_of_ne hi]
      exact hs i
  · intro i hi
    have h557 : i ≠ 557 := by
      intro h
      subst i
      exact hi ⟨217, rfl⟩
    have h625 : i ≠ 625 := by
      intro h
      subst i
      exact hi ⟨285, rfl⟩
    simp [SubexpSetupStorage.copyState, StackRoutines.copyStacks, h557, h625]

/-- The joined input uses the existing low256 words and exactly38 empty
private words; retained caller masters are outside this interval. -/
theorem joined_shape_of_high_empty (a : OuterData)
    (hempty : ∀ i : Fin 38,
      a.stacks (joinedPort (QueryProducerSpace.Native.producerPorts i)) = []) :
    ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs
        (fun j : Fin 256 => a.stacks (joinedPort (j.castAdd 38)))
        (QueryProducerSpace.Native.emptyHigh [])).stacks i := by
  intro i
  refine Fin.addCases (m := 256) (n := 38) (fun j => ?_) (fun j => ?_) i
  · simp [QueryProducerSpace.Native.joinedState]
  · simp only [QueryProducerSpace.Native.joinedState, Fin.addCases_right]
    change a.stacks (joinedPort (QueryProducerSpace.Native.producerPorts j)) = _
    rw [hempty]
    fin_cases j <;> rfl

def specializeCall : OuterCode :=
  .seq (SubexpSetupStorage.copyCmd 857 625 881)
    (liftCommand QueryProducerSpace.Native.command 205 217 id joinedPort)

def lowPayload : OuterCode := .seq (liftBase LeafProgram.Source.command) specializeCall

def literalPayload : OuterCode :=
  .seq (liftInner (readFlag 234)) (.ite 15 (liftInner highConstant) lowPayload)

def literalIteration : OuterCode :=
  .seq (liftInner makeLiteralKey) (.seq literalPayload (liftInner finishLiteral))

def literalPorts : UnaryForPrograms.Ports 16 896 := ⟨573,0,1⟩

def prepareFactor : OuterCode :=
  .seq (liftInner (copy 212 233))
    (.seq (UnaryForPrograms.forCmd literalPorts literalIteration)
      (liftInner (move 229 221)))

structure ExecutesOuter (code : OuterCode) (K : ℕ) (before after : OuterStore) : Prop where
  run : ∀ regs : Fin 16 → Bool, ∃ k rf, k≤K ∧
    Eval code k (⟨regs,before⟩ : OuterData) (⟨rf,after⟩ : OuterData)

theorem ExecutesOuter.seq {a b : OuterCode} {Ka Kb : ℕ} {s u v : OuterStore}
    (ha : ExecutesOuter a Ka s u) (hb : ExecutesOuter b Kb u v) :
    ExecutesOuter (.seq a b) (Ka+Kb) s v := by
  constructor
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha.run regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb.run ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem ExecutesOuter.mono {a : OuterCode} {Ka Kb : ℕ} {s u : OuterStore}
    (ha : ExecutesOuter a Ka s u) (h : Ka≤Kb) : ExecutesOuter a Kb s u := by
  constructor
  intro regs
  obtain ⟨n,r,hn,he⟩ := ha.run regs
  exact ⟨n,r,hn.trans h,he⟩

def projectInner (s : OuterStore) : Store := s ∘ innerPort

noncomputable def replaceInner (s : OuterStore) (u : Store) : OuterStore := Function.extend innerPort u s

theorem replaceInner_project (s : OuterStore) : replaceInner s (projectInner s)=s := by
  have h := embedState_project id innerPort (⟨fun _=>false,s⟩ : OuterData)
    Function.injective_id innerPort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceInner_update (s : OuterStore) (u : Store) (i : Fin 256) (bits : List Bool) :
    replaceInner s (Function.update u i bits)=Function.update (replaceInner s u) (innerPort i) bits :=
  ProgramLinking.extend_update innerPort_injective _ _ _ _

theorem liftInner_run (s : OuterStore) (code : Code) (K : ℕ) (u : Store)
    (h : ExecutesIn code K (projectInner s) u) :
    ExecutesOuter (liftInner code) (K+1) s (replaceInner s u) := by
  constructor
  intro regs
  obtain ⟨k,rf,hk,he⟩ := h regs
  have hl := eval_liftCommand_from_state code 0 0 id innerPort (⟨regs,s⟩ : OuterData)
    Function.injective_id innerPort_injective he
  refine ⟨k+1,rf,by omega,?_⟩
  unfold liftInner
  convert hl using 1
  apply state_ext
  · simp [embedState]
  · rfl

/-- A common single-result service remains a single-result service after
relocation, with the exact one-step compiled-call overhead. -/
theorem liftInner_update_run (s : OuterStore) (code : Code) (K : ℕ)
    (i : Fin 256) (bits : List Bool)
    (h : ExecutesIn code K (projectInner s) (Function.update (projectInner s) i bits)) :
    ExecutesOuter (liftInner code) (K+1) s (Function.update s (innerPort i) bits) := by
  have hh := liftInner_run s code K _ h
  simpa only [replaceInner_update,replaceInner_project] using hh

def projectBase (s : OuterStore) : PerturbationAssembly.OuterStore := s ∘ basePort

noncomputable def replaceBase (s : OuterStore) (u : PerturbationAssembly.OuterStore) : OuterStore :=
  Function.extend basePort u s

theorem projectInner_projectBase (s : OuterStore) :
    PerturbationAssembly.projectInner (projectBase s) = projectInner s := by
  funext i
  exact congrArg s (basePort_inner i)

theorem projectBase_update (s : OuterStore) (i : Fin 768) (word : List Bool) :
    projectBase (Function.update s (basePort i) word) = Function.update (projectBase s) i word := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [projectBase]
  · have hne : basePort j ≠ basePort i := fun h => hj (basePort_injective h)
    simp [projectBase, Function.comp_def, hj, hne]

theorem replaceBase_project (s : OuterStore) : replaceBase s (projectBase s) = s := by
  have h := embedState_project id basePort (⟨fun _ => false, s⟩ : OuterData)
    Function.injective_id basePort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceBase_update (s : OuterStore) (u : PerturbationAssembly.OuterStore)
    (i : Fin 768) (bits : List Bool) :
    replaceBase s (Function.update u i bits) = Function.update (replaceBase s u) (basePort i) bits :=
  ProgramLinking.extend_update basePort_injective _ _ _ _

theorem liftBase_run (s : OuterStore) (code : Cmd 16 768) (K : ℕ)
    (u : PerturbationAssembly.OuterStore)
    (h : PerturbationAssembly.ExecutesOuter code K (projectBase s) u) :
    ExecutesOuter (liftBase code) (K+1) s (replaceBase s u) := by
  constructor
  intro regs
  obtain ⟨k,rf,hk,he⟩ := h regs
  have hl := eval_liftCommand_from_state code 0 0 id basePort (⟨regs,s⟩ : OuterData)
    Function.injective_id basePort_injective he
  refine ⟨k+1,rf,by omega,?_⟩
  unfold liftBase
  convert hl using 1
  apply state_ext
  · simp [embedState]
  · rfl

theorem liftBase_update_run (s : OuterStore) (code : Cmd 16 768) (K : ℕ)
    (i : Fin 768) (bits : List Bool)
    (h : PerturbationAssembly.ExecutesOuter code K (projectBase s)
      (Function.update (projectBase s) i bits)) :
    ExecutesOuter (liftBase code) (K+1) s (Function.update s (basePort i) bits) := by
  have hh := liftBase_run s code K _ h
  simpa only [replaceBase_update,replaceBase_project] using hh

/-- This is the actual three-stage low path, including one mask copy per
invocation. The source and producer witnesses name fixed concrete commands. -/
theorem lowPayload_eval (a : OuterData) (b : State 16 768) (c : State 16 294)
    (sourceSteps producerSteps : ℕ)
    (hsource : Eval LeafProgram.Source.command sourceSteps (projectState id basePort a) b)
    (htmp : (embedState id basePort a b).stacks 881 = [])
    (hproducer : Eval QueryProducerSpace.Native.command producerSteps
      (projectState id joinedPort
        (SubexpSetupStorage.copyState 857 625 (embedState id basePort a b))) c) :
    Eval lowPayload (sourceSteps+1+
      (7*((embedState id basePort a b).stacks 857).length+5+(producerSteps+1))) a
      (embedState id joinedPort
        (SubexpSetupStorage.copyState 857 625 (embedState id basePort a b)) c) := by
  have hs := eval_liftCommand_from_state LeafProgram.Source.command 0 0 id basePort a
    Function.injective_id basePort_injective hsource
  have hc := SubexpSetupStorage.copy_eval 857 625 881 (embedState id basePort a b)
    (by decide) (by decide) (by decide) htmp
  have hp := eval_liftCommand_from_state QueryProducerSpace.Native.command 205 217 id joinedPort
    (SubexpSetupStorage.copyState 857 625 (embedState id basePort a b))
    Function.injective_id joinedPort_injective hproducer
  exact hs.seq (hc.seq hp)

def literalReady (s : OuterStore) (count acc : List Bool) : OuterStore :=
  Function.update (Function.update s 573 count) 569 acc

def tableRecord (payload : ℕ → List Bool) (j : ℕ) : List Bool :=
  Encoding.frame (Encoding.encodeNat j) ++ Encoding.frame (payload j)

def tableResult (payload : ℕ → List Bool) : ℕ → List Bool → List Bool
  | 0,acc => acc
  | n+1,acc => tableResult payload n (tableRecord payload n ++ acc)

theorem literalPopped (s : OuterStore) (count acc : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped literalPorts (⟨regs,literalReady s count acc⟩ : OuterData)=
      (⟨readRegs regs 0 1 count.head?,literalReady s count.tail acc⟩ : OuterData) := by
  apply state_ext
  · simp [UnaryForPrograms.popped,literalPorts,literalReady]
  · funext i
    by_cases h573 : i=573 <;> by_cases h569 : i=569 <;>
      simp [UnaryForPrograms.popped, literalPorts, literalReady, h573, h569]

/-- The table is built by n paid invocations, in descending variable order.
The callback premise is for one fixed command and is discharged by the
literal source/branch/low-worker composition. -/
theorem literalLoop_run (s : OuterStore) (body : OuterCode) (payload : ℕ → List Bool)
    (K n : ℕ)
    (hbody : ∀ j,j<n → ∀ acc, ExecutesOuter body K
      (literalReady s (List.replicate j true) acc)
      (literalReady s (List.replicate j true) (tableRecord payload j ++ acc))) :
    ∀ j,j≤n → ∀ acc, ExecutesOuter (UnaryForPrograms.forCmd literalPorts body)
      (j*(K+2)+2) (literalReady s (List.replicate j true) acc)
      (literalReady s [] (tableResult payload j acc)) := by
  intro j hj acc
  constructor
  intro regs
  suffices h : ∃ costs k rf, UnaryForPrograms.Visits literalPorts body costs k
      (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
      (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) ∧ k≤j*(K+2)+2 by
    obtain ⟨costs,k,rf,hv,hk⟩ := h
    exact ⟨k,rf,hk,hv.eval⟩
  induction j generalizing acc regs with
  | zero =>
      refine ⟨[],2,readRegs regs 0 1 none,?_,by simp⟩
      simpa [literalPopped,tableResult] using
        UnaryForPrograms.Visits.done (p:=literalPorts) (body:=body)
          (⟨regs,literalReady s [] acc⟩ : OuterData) (by simp [literalReady,literalPorts])
  | succ j ih =>
      obtain ⟨nb,rb,hnb,heb⟩ := (hbody j (by omega) acc).run (readRegs regs 0 1 (some true))
      obtain ⟨costs,nt,rt,ht,hnt⟩ := ih (by omega) (tableRecord payload j ++ acc) rb
      refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
      · have hv := UnaryForPrograms.Visits.step (p:=literalPorts) (body:=body)
          (d:=(⟨regs,literalReady s (List.replicate (j+1) true) acc⟩ : OuterData))
          (by simp [literalReady,literalPorts])
          (by simpa only [literalPopped,List.replicate_succ,List.head?_cons,List.tail_cons] using heb)
          (by simp [literalReady,literalPorts,UnaryForPrograms.popped,List.replicate_succ]) ht
        simpa only [tableResult] using hv
      · nlinarith


theorem tableResult_eq (payload : ℕ → List Bool) (n : ℕ) (acc : List Bool) :
    tableResult payload n acc=(List.range n).flatMap (tableRecord payload) ++ acc := by
  induction n generalizing acc with
  | zero => simp [tableResult]
  | succ n ih => simp [tableResult,ih,List.range_succ,List.flatMap_append,List.append_assoc]


theorem readFlag_outer (s : OuterStore) (source : Fin 256)
    (hsrc : source≠222) (hsrc' : source≠223) (h120s : source≠120)
    (h120 : s 460=[]) (h222 : s 562=[]) (h223 : s 563=[])
    (regs : Fin 16 → Bool) :
    ∃ k rf,k≤10*(s 573).length+9*(s (innerPort source)).length+17 ∧
      Eval (liftInner (readFlag source)) k (⟨regs,s⟩ : OuterData) (⟨rf,s⟩ : OuterData) ∧
      rf 15=(s (innerPort source)).getD (s 573).length false := by
  obtain ⟨k,rf,hk,he,hf⟩ := readFlag_eval (projectInner s) source hsrc hsrc' h120s
    (by simpa [projectInner,Function.comp_def,innerPort] using h120)
    (by simpa [projectInner,Function.comp_def,innerPort] using h222)
    (by simpa [projectInner,Function.comp_def,innerPort] using h223) regs
  have hl := eval_liftCommand_from_state (readFlag source) 0 0 id innerPort
    (⟨regs,s⟩ : OuterData) Function.injective_id innerPort_injective he
  have hout : embedState id innerPort (⟨regs,s⟩ : OuterData)
      (⟨rf,projectInner s⟩ : Data)=(⟨rf,s⟩ : OuterData) := by
    apply state_ext
    · simp [embedState]
    · exact replaceInner_project s
  rw [hout] at hl
  refine ⟨k+1,rf,?_,hl,?_⟩
  · simpa [projectInner,Function.comp_def,innerPort] using Nat.add_le_add_right hk 1
  · simpa [projectInner,Function.comp_def,innerPort] using hf


/-- Actual high-mask dispatch. Its low execution is the fixed source,
mask copy and immediate specialization command defined above. -/
theorem literalPayload_run (s : OuterStore) (n W Klow : ℕ) (rows payload : List Bool)
    (hn : (s 552).length=n) (hm : (s 575).length=n)
    (hzero : (s 547).length=W) (hone : (s 548).length=W)
    (h220 : s 560=[]) (he : ∀ i∈originScratch,s (innerPort i)=[])
    (hlow : ExecutesOuter lowPayload Klow s
      (Function.update (Function.update s 545 rows) 557 payload)) :
    ExecutesOuter literalPayload
      (10*(s 573).length+9*(s 574).length+18 +
        (10*(s 573).length+42*n+29*W+109) + Klow) s
      (if (s 574).getD (s 573).length false then
        Function.update s 557 (Encoding.frame (originKey n)++
          Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)++s 557)
       else Function.update (Function.update s 545 rows) 557 payload) := by
  constructor
  intro regs
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_outer s 234 (by decide) (by decide) (by decide)
    (by simpa [innerPort] using he 120 (by simp [originScratch]))
    (by simpa [innerPort] using he 222 (by simp [originScratch]))
    (by simpa [innerPort] using he 223 (by simp [originScratch])) regs
  change nr ≤ 10*(s 573).length+9*(s 574).length+17 at hnr
  change rr 15=(s 574).getD (s 573).length false at hbit
  cases hb:(s 574).getD (s 573).length false with
  | false =>
      obtain ⟨nl,rl,hnl,hel⟩ := hlow.run rr
      have hflag : rr 15=false := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_false (yes:=liftInner highConstant) hflag hel)
      refine ⟨nr+(nl+1),rl,by omega,?_⟩
      simpa [literalPayload,hb,innerPort] using hrun
  | true =>
      have hh := highConstant_run (projectInner s) n W
        (by simpa [projectInner,Function.comp_def,innerPort] using hn)
        (by simpa [projectInner,Function.comp_def,innerPort] using hm)
        (by simpa [projectInner,Function.comp_def,innerPort] using hzero)
        (by simpa [projectInner,Function.comp_def,innerPort] using hone)
        (by simpa [projectInner,Function.comp_def,innerPort] using h220)
        (by simpa [projectInner,Function.comp_def] using he)
      have hhl := liftInner_update_run s highConstant _ 217 _ hh
      obtain ⟨nh,rh,hnh,heh⟩ := hhl.run rr
      change nh ≤ (10*(s 573).length+42*n+29*W+108)+1 at hnh
      have hflag : rr 15=true := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_true (no:=lowPayload) hflag heh)
      refine ⟨nr+(nh+1),rh,?_,?_⟩
      · omega
      · simpa [literalPayload,hb,innerPort,projectInner,Function.comp_def] using hrun


/-- Literal control skeleton. The payload premise is discharged by the native
branch/source/low preparation theorem, rather than a supplied table. -/
theorem literalIteration_run (s : OuterStore) (j K : ℕ)
    (rows payload : List Bool)
    (hj : s 573=List.replicate j true)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hpayload : ExecutesOuter literalPayload K
      (Function.update s 555 (Encoding.encodeNat j))
      (Function.update (Function.update (Function.update s 555 (Encoding.encodeNat j))
        545 rows) 557 payload)) :
    ExecutesOuter literalIteration
      (7*j+K+22*(j+1)+19*payload.length+2*rows.length+54) s
      (Function.update s 569 (Encoding.frame (Encoding.encodeNat j)++
        Encoding.frame payload++s 569)) := by
  let key := Encoding.encodeNat j
  let a := Function.update s 555 key
  let b := Function.update (Function.update a 545 rows) 557 payload
  have hkey : ExecutesOuter (liftInner makeLiteralKey) (7*j+8) s a := by
    have h := liftInner_update_run s makeLiteralKey (7*j+7) 215 key
      (makeLiteralKey_run (projectInner s) j
        (by simpa [projectInner,Function.comp_def,innerPort] using hj)
        (by simpa [projectInner,Function.comp_def,innerPort] using h555)
        (by simpa [projectInner,Function.comp_def,innerPort] using he 120 (by simp [entryScratch])))
    simpa [a,innerPort] using h
  have hb : ∀ i∈entryScratch,(projectInner b) i=[] := by
    intro i hi
    have hn : innerPort i≠555 ∧ innerPort i≠545 ∧ innerPort i≠557 := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [b,a,projectInner,Function.comp_def,Function.update_apply,hn.1,hn.2.1,hn.2.2] using he i hi
  have hend := liftInner_run b finishLiteral
    (22*key.length+19*payload.length+2*rows.length+45)
    (Function.update (Function.update (Function.update (Function.update (projectInner b) 217 [])
      229 (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++
        (projectInner b) 229)) 215 []) 205 [])
    (by simpa [projectInner,Function.comp_def,innerPort,b,a] using finishLiteral_run (projectInner b) hb)
  rw [replaceInner_update,replaceInner_update,replaceInner_update,replaceInner_update,
    replaceInner_project] at hend
  have hout : Function.update (Function.update (Function.update (Function.update b
      (innerPort 217) []) (innerPort 229)
      (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++(projectInner b) 229))
      (innerPort 215) []) (innerPort 205) []=
      Function.update s 569 (Encoding.frame key++Encoding.frame payload++s 569) := by
    funext i
    by_cases h545' : i=545
    · subst i; simp [innerPort,h545]
    by_cases h555' : i=555
    · subst i; simp [innerPort,h555]
    by_cases h557' : i=557
    · subst i; simp [innerPort,h557]
    by_cases h569' : i=569
    · subst i; simp [innerPort, projectInner, b, a]
    simp [innerPort, projectInner, b, a, h545', h555', h557', h569']
  rw [hout] at hend
  have h := hkey.seq (hpayload.seq hend)
  unfold literalIteration
  convert h using 1
  simp [key, Encoding.encodeNat]
  omega

theorem literalPayload_rel (s : OuterStore) (n W Klow Lrows Lpayload : ℕ) (Good : List Bool → Prop)
    (hn : (s 552).length=n) (hm : (s 575).length=n)
    (hzero : (s 547).length=W) (hone : (s 548).length=W)
    (h545 : s 545=[]) (h557 : s 557=[]) (h220 : s 560=[])
    (he : ∀ i∈originScratch,s (innerPort i)=[])
    (hlow : (s 574).getD (s 573).length false=false →
      ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k≤Klow ∧ words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval lowPayload k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData))
    (hhigh : (s 574).getD (s 573).length false=true →
      Good (Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)))
    (hhighLength : (Encoding.frame (originKey n)++
      Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)).length≤Lpayload)
    (regs : Fin 16 → Bool) :
    ∃ words payload k rf,
      k≤10*(s 573).length+9*(s 574).length+18+
        (10*(s 573).length+42*n+29*W+109)+Klow ∧
      words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval literalPayload k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData) := by
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_outer s 234 (by decide) (by decide) (by decide)
    (by simpa [innerPort] using he 120 (by simp [originScratch]))
    (by simpa [innerPort] using he 222 (by simp [originScratch]))
    (by simpa [innerPort] using he 223 (by simp [originScratch])) regs
  change nr≤10*(s 573).length+9*(s 574).length+17 at hnr
  change rr 15=(s 574).getD (s 573).length false at hbit
  cases hb:(s 574).getD (s 573).length false with
  | false =>
      obtain ⟨words,payload,nl,rl,hnl,hw,hp,hgood,hel⟩ := hlow hb rr
      have hflag : rr 15=false := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_false (yes:=liftInner highConstant) hflag hel)
      refine ⟨words,payload,nr+(nl+1),rl,by omega,hw,hp,hgood,?_⟩
      simpa [literalPayload,innerPort] using hrun
  | true =>
      let payload := Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)
      have hh := highConstant_run (projectInner s) n W
        (by simpa [projectInner,Function.comp_def,innerPort] using hn)
        (by simpa [projectInner,Function.comp_def,innerPort] using hm)
        (by simpa [projectInner,Function.comp_def,innerPort] using hzero)
        (by simpa [projectInner,Function.comp_def,innerPort] using hone)
        (by simpa [projectInner,Function.comp_def,innerPort] using h220)
        (by simpa [projectInner,Function.comp_def] using he)
      obtain ⟨nh,rh,hnh,heh⟩ := (liftInner_update_run s highConstant _ 217 _ hh).run rr
      change nh≤(10*(s 573).length+42*n+29*W+108)+1 at hnh
      have hflag : rr 15=true := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_true (no:=lowPayload) hflag heh)
      refine ⟨[],payload,nr+(nh+1),rh,by omega,by simp,hhighLength,hhigh hb,?_⟩
      have hz : Function.update s 545 []=s := by simpa only [←h545] using Function.update_eq_self 545 s
      simpa [literalPayload,innerPort,projectInner,Function.comp_def,payload,h557,hz] using hrun

theorem literalIteration_rel (s : OuterStore) (j K Lrows Lpayload : ℕ)
    (Good : List Bool → Prop)
    (hj : s 573=List.replicate j true)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hpayload : ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k≤K ∧ words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval literalPayload k
        (⟨regs,Function.update s 555 (Encoding.encodeNat j)⟩ : OuterData)
        (⟨rf,Function.update (Function.update (Function.update s 555 (Encoding.encodeNat j))
          545 words) 557 payload⟩ : OuterData))
    (regs : Fin 16 → Bool) :
    ∃ payload k rf,k≤7*j+K+22*(j+1)+19*Lpayload+2*Lrows+54 ∧
      payload.length≤Lpayload ∧ Good payload ∧
      Eval literalIteration k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 569 (Encoding.frame (Encoding.encodeNat j)++
          Encoding.frame payload++s 569)⟩ : OuterData) := by
  let key := Encoding.encodeNat j
  let a := Function.update s 555 key
  have hkey : ExecutesOuter (liftInner makeLiteralKey) (7*j+8) s a := by
    have h := liftInner_update_run s makeLiteralKey (7*j+7) 215 key
      (makeLiteralKey_run (projectInner s) j
        (by simpa [projectInner,Function.comp_def,innerPort] using hj)
        (by simpa [projectInner,Function.comp_def,innerPort] using h555)
        (by simpa [projectInner,Function.comp_def,innerPort] using he 120 (by simp [entryScratch])))
    simpa [a,innerPort] using h
  obtain ⟨nk,rk,hnk,hek⟩ := hkey.run regs
  obtain ⟨words,payload,np,rp,hnp,hw,hp,hgood,hep⟩ := hpayload rk
  let b := Function.update (Function.update a 545 words) 557 payload
  have hb : ∀ i∈entryScratch,(projectInner b) i=[] := by
    intro i hi
    have hn : innerPort i≠555 ∧ innerPort i≠545 ∧ innerPort i≠557 := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [b,a,projectInner,Function.comp_def,Function.update_apply,hn.1,hn.2.1,hn.2.2] using he i hi
  have hend := liftInner_run b finishLiteral
    (22*key.length+19*payload.length+2*words.length+45)
    (Function.update (Function.update (Function.update (Function.update (projectInner b) 217 [])
      229 (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++
        (projectInner b) 229)) 215 []) 205 [])
    (by simpa [projectInner,Function.comp_def,innerPort,b,a] using finishLiteral_run (projectInner b) hb)
  rw [replaceInner_update,replaceInner_update,replaceInner_update,replaceInner_update,
    replaceInner_project] at hend
  have hout : Function.update (Function.update (Function.update (Function.update b
      (innerPort 217) []) (innerPort 229)
      (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++(projectInner b) 229))
      (innerPort 215) []) (innerPort 205) []=
      Function.update s 569 (Encoding.frame key++Encoding.frame payload++s 569) := by
    funext i
    by_cases h545' : i=545
    · subst i; simp [innerPort,h545]
    by_cases h555' : i=555
    · subst i; simp [innerPort,h555]
    by_cases h557' : i=557
    · subst i; simp [innerPort,h557]
    by_cases h569' : i=569
    · subst i; simp [innerPort, projectInner, b, a]
    simp [innerPort, projectInner, b, a, h545', h555', h557', h569']
  rw [hout] at hend
  obtain ⟨nf,rf,hnf,hef⟩ := hend.run rp
  refine ⟨payload,nk+(np+nf),rf,?_,hp,hgood,hek.seq (hep.seq hef)⟩
  simp only [key,Encoding.encodeNat,List.length_append,List.length_replicate,List.length_singleton] at hnf
  omega


/-- Full counted table traversal, including paid master copy and output move.
The per-literal premise is a trace for the actual fixed literalIteration.
No loop or table construction is left as a semantic operation. -/
theorem prepareFactor_run (s : OuterStore) (payload : ℕ → List Bool)
    (K n : ℕ) (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : ∀ j,j<n → ∀ acc, ExecutesOuter literalIteration K
      (literalReady s (List.replicate j true) acc)
      (literalReady s (List.replicate j true) (tableRecord payload j ++ acc))) :
    ExecutesOuter prepareFactor
      (7*n+n*(K+2)+6*(tableResult payload n []).length+15) s
      (Function.update s 561 (tableResult payload n [])) := by
  let a := literalReady s (List.replicate n true) []
  let b := literalReady s [] (tableResult payload n [])
  have hc : ExecutesOuter (liftInner (copy 212 233)) (7*n+6) s a := by
    have h := liftInner_update_run s (copy 212 233) (7*n+5) 233 (List.replicate n true) (by
      simpa [projectInner,Function.comp_def,innerPort,hn,h573] using
        copy_run 212 233 (projectInner s) (by decide) (by decide) (by decide)
          (by simpa [projectInner,Function.comp_def,innerPort] using h460))
    have heq : Function.update s (innerPort 233) (List.replicate n true)=a := by
      funext i
      by_cases hi : i=569 <;> simp [a,literalReady,Function.update_apply,innerPort,hi,h569]
    simpa [heq] using h
  have hl : ExecutesOuter (UnaryForPrograms.forCmd literalPorts literalIteration)
      (n*(K+2)+2) a b := literalLoop_run s literalIteration payload K n hbody n (by omega) []
  have hm : ExecutesOuter (liftInner (SubexpPolynomialConstructor.move 229 221))
      (6*(tableResult payload n []).length+7) b
      (Function.update s 561 (tableResult payload n [])) := by
    have h := liftInner_run b (SubexpPolynomialConstructor.move 229 221)
      (6*(tableResult payload n []).length+6)
      (Function.update (Function.update (projectInner b) 229 []) 221 (tableResult payload n [])) (by
        simpa [projectInner,Function.comp_def,innerPort,b,literalReady] using
          SubexpPolynomialConstructor.move_run (projectInner b) 229 221
            (by decide) (by decide) (by decide)
            (by simp [projectInner, innerPort, b, literalReady, h585])
            (by simp [projectInner, innerPort, b, literalReady, h561]))
    rw [replaceInner_update,replaceInner_update,replaceInner_project] at h
    convert h using 1
    funext i
    by_cases h561' : i=561
    · subst i; simp [innerPort]
    by_cases h569' : i=569
    · subst i; simp [innerPort,h569]
    by_cases h573' : i=573
    · subst i; simp [innerPort,b,literalReady,h573]
    simp [innerPort, b, literalReady, h561', h569', h573']
  have h := hc.seq (hl.seq hm)
  unfold prepareFactor
  convert h using 1
  omega


theorem tableResult_original (payload : ℕ → List Bool) (n : ℕ) (acc : List Bool) :
    tableResult payload n acc = PerturbationAssembly.tableResult payload n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simpa only [tableResult, PerturbationAssembly.tableResult, tableRecord,
      PerturbationAssembly.tableRecord] using ih (tableRecord payload n ++ acc)

/-- Every ambient coordinate has exactly one framed lookup entry, including
unused coordinates and high coordinates. -/
theorem tableResult_incidence (payload : ℕ → List Bool) (n : ℕ) :
    tableResult payload n [] = Squarefree.Program.lookupRecords
      (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n) => payload v.val) ()) := by
  rw [tableResult_original]
  exact PerturbationAssembly.tableResult_incidence payload n

/-- The accumulator retains only n specialized payloads; the native loop
counter is unary ambient n, never an exponential assignment list. -/
theorem tableResult_length_bound (payload : ℕ → List Bool) (L n : ℕ)
    (h : ∀ j, j<n → (payload j).length ≤ L) (acc : List Bool) :
    (tableResult payload n acc).length ≤ acc.length+n*(2*n+2*L+4) := by
  induction n generalizing acc with
  | zero => simp [tableResult]
  | succ n ih =>
      have ht := ih (fun j hj => h j (by omega)) (tableRecord payload n ++ acc)
      have hn := h n (by omega)
      simp only [tableResult, tableRecord, List.length_append, Encoding.length_frame,
        Encoding.encodeNat, List.length_replicate, List.length_cons, List.length_nil] at *
      nlinarith

/-- Space for one framed original-variable ID and one bounded payload. -/
def literalRecordBound (n L : ℕ) : ℕ := 2*n+2*L+4

/-- The payload is existential after the actual incoming registers, not before
all executions. The accumulator bound is the complete table's size bound. -/
structure RelLiteralBody (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ) : Prop where
  run : ∀ j, j<n → ∀ acc, acc.length≤n*literalRecordBound n L →
    ∀ regs : Fin 16 → Bool, ∃ bits k rf,
      k≤K ∧ bits.length≤L ∧ P j bits ∧
      Eval body k (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits++acc)⟩ : OuterData)

theorem literalRecord_length_le (n L j : ℕ) (hj : j<n)
    (bits : List Bool) (hb : bits.length≤L) :
    (Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits).length≤
      literalRecordBound n L := by
  simp only [List.length_append,Encoding.length_frame,Encoding.encodeNat,
    List.length_replicate,List.length_singleton,literalRecordBound]
  omega

theorem rel_tableResult_congr (f g : ℕ → List Bool) (j : ℕ)
    (h : ∀ i,i<j → f i=g i) (acc : List Bool) :
    tableResult f j acc=tableResult g j acc := by
  induction j generalizing acc with
  | zero => rfl
  | succ j ih =>
      have he : tableRecord f j=tableRecord g j := by
        simp only [tableRecord,h j (by omega)]
      simp only [tableResult,he]
      exact ih (fun i hi=>h i (by omega)) _

theorem rel_tableResult_length_le (f : ℕ → List Bool) (n L j : ℕ)
    (hj : j≤n) (h : ∀ i,i<j → (f i).length≤L) (acc : List Bool) :
    (tableResult f j acc).length≤acc.length+j*literalRecordBound n L := by
  induction j generalizing acc with
  | zero => simp [tableResult]
  | succ j ih =>
      have hr := literalRecord_length_le n L j (by omega) (f j) (h j (by omega))
      have ht := ih (by omega) (fun i hi=>h i (by omega)) (tableRecord f j++acc)
      change (tableRecord f j).length≤literalRecordBound n L at hr
      simp only [tableResult,List.length_append] at ht ⊢
      nlinarith

/-- Every witness is chosen along this actual run. The capacity invariant
reserves room for all remaining records before invoking the bounded body. -/
theorem literalLoop_rel_visits (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (j : ℕ) (hj : j≤n) (acc : List Bool)
    (hcap : acc.length+j*literalRecordBound n L≤n*literalRecordBound n L)
    (regs : Fin 16 → Bool) :
    ∃ payload costs k rf,
      (∀ i,i<j → (payload i).length≤L ∧ P i (payload i)) ∧
      k≤j*(K+2)+2 ∧
      UnaryForPrograms.Visits literalPorts body costs k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) := by
  induction j generalizing acc regs with
  | zero =>
      refine ⟨fun _=>[],[],2,readRegs regs 0 1 none,?_,by simp,?_⟩
      · intro i hi; omega
      · simpa [literalPopped,tableResult] using
          UnaryForPrograms.Visits.done (p:=literalPorts) (body:=body)
            (⟨regs,literalReady s [] acc⟩ : OuterData) (by simp [literalReady,literalPorts])
  | succ j ih =>
      have hac : acc.length≤n*literalRecordBound n L := by nlinarith
      obtain ⟨bits,kb,rb,hkb,hbits,hP,hbe⟩ :=
        hbody.run j (by omega) acc hac (readRegs regs 0 1 (some true))
      let next := Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits++acc
      have hr := literalRecord_length_le n L j (by omega) bits hbits
      have hn : next.length≤literalRecordBound n L+acc.length := by
        simpa only [next,List.length_append] using Nat.add_le_add_right hr acc.length
      have hnext : next.length+j*literalRecordBound n L≤n*literalRecordBound n L := by
        nlinarith
      obtain ⟨f,costs,kt,rt,hf,hkt,ht⟩ := ih (by omega) next hnext rb
      let payload := Function.update f j bits
      have hp : ∀ i,i<j+1 → (payload i).length≤L ∧ P i (payload i) := by
        intro i hi
        by_cases he : i=j
        · subst i; simpa [payload] using And.intro hbits hP
        · simpa [payload,he] using hf i (by omega)
      have htable : tableResult payload (j+1) acc=tableResult f j next := by
        change tableResult payload j (tableRecord payload j++acc)=_
        have he : tableRecord payload j++acc=next := by
          simp [payload,tableRecord,next,List.append_assoc]
        rw [he]
        apply rel_tableResult_congr
        intro i hi
        simp [payload,show i≠j by omega]
      refine ⟨payload,kb::costs,kb+kt+2,rt,hp,?_,?_⟩
      · nlinarith
      · rw [htable]
        apply UnaryForPrograms.Visits.step (p:=literalPorts) (body:=body)
          (d:=(⟨regs,literalReady s (List.replicate (j+1) true) acc⟩ : OuterData))
          (by simp [literalReady,literalPorts])
          (by simpa only [literalPopped,List.replicate_succ,List.head?_cons,List.tail_cons,next] using hbe)
          (by simp [literalReady,literalPorts,UnaryForPrograms.popped,List.replicate_succ]) ht

/-- Relational counted loop with an explicit actual-register execution. -/
theorem literalLoop_rel_run (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (j : ℕ) (hj : j≤n) (acc : List Bool)
    (hcap : acc.length+j*literalRecordBound n L≤n*literalRecordBound n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ i,i<j → (payload i).length≤L ∧ P i (payload i)) ∧
      k≤j*(K+2)+2 ∧
      Eval (UnaryForPrograms.forCmd literalPorts body) k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) := by
  obtain ⟨payload,costs,k,rf,hp,hk,hv⟩ :=
    literalLoop_rel_visits s body P K n L hbody j hj acc hcap regs
  exact ⟨payload,k,rf,hp,hk,hv.eval⟩

/-- Full native table producer with actual-run witnesses, measured master copy,
loop, and output move. No payload family uniform over registers is required. -/
theorem prepareFactor_rel_run (s : OuterStore) (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : RelLiteralBody s literalIteration P K n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j<n → (payload j).length≤L ∧ P j (payload j)) ∧
      k≤7*n+n*(K+2)+6*n*literalRecordBound n L+15 ∧
      Eval prepareFactor k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (tableResult payload n [])⟩ : OuterData) := by
  let a := literalReady s (List.replicate n true) []
  have hc : ExecutesOuter (liftInner (copy 212 233)) (7*n+6) s a := by
    have h := liftInner_update_run s (copy 212 233) (7*n+5) 233 (List.replicate n true) (by
      simpa [projectInner,Function.comp_def,innerPort,hn,h573] using
        copy_run 212 233 (projectInner s) (by decide) (by decide) (by decide)
          (by simpa [projectInner,Function.comp_def,innerPort] using h460))
    have heq : Function.update s (innerPort 233) (List.replicate n true)=a := by
      funext i
      by_cases hi : i=569 <;> simp [a,literalReady,Function.update_apply,innerPort,hi,h569]
    simpa [heq] using h
  obtain ⟨kc,rc,hkc,hec⟩ := hc.run regs
  obtain ⟨payload,kl,rl,hp,hkl,hel⟩ :=
    literalLoop_rel_run s literalIteration P K n L hbody n (by omega) [] (by simp) rc
  let b := literalReady s [] (tableResult payload n [])
  have hm : ExecutesOuter (liftInner (SubexpPolynomialConstructor.move 229 221))
      (6*(tableResult payload n []).length+7) b
      (Function.update s 561 (tableResult payload n [])) := by
    have h := liftInner_run b (SubexpPolynomialConstructor.move 229 221)
      (6*(tableResult payload n []).length+6)
      (Function.update (Function.update (projectInner b) 229 []) 221 (tableResult payload n [])) (by
        simpa [projectInner,Function.comp_def,innerPort,b,literalReady] using
          SubexpPolynomialConstructor.move_run (projectInner b) 229 221
            (by decide) (by decide) (by decide)
            (by simp [projectInner, innerPort, b, literalReady, h585])
            (by simp [projectInner, innerPort, b, literalReady, h561]))
    rw [replaceInner_update,replaceInner_update,replaceInner_project] at h
    convert h using 1
    funext i
    by_cases h561' : i=561
    · subst i; simp [innerPort]
    by_cases h569' : i=569
    · subst i; simp [innerPort,h569]
    by_cases h573' : i=573
    · subst i; simp [innerPort,b,literalReady,h573]
    simp [innerPort, b, literalReady, h561', h569', h573']
  obtain ⟨km,rm,hkm,hem⟩ := hm.run rl
  have hlen := rel_tableResult_length_le payload n L n (by omega) (fun i hi=>(hp i hi).1) []
  simp only [List.length_nil,Nat.zero_add] at hlen
  refine ⟨payload,kc+(kl+km),rm,hp,?_,hec.seq (hel.seq hem)⟩
  nlinarith

/-- Exact lookup-table serialization of the actual relational output. -/
theorem prepareFactor_rel_lookup (s : OuterStore) (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : RelLiteralBody s literalIteration P K n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j<n → (payload j).length≤L ∧ P j (payload j)) ∧
      k≤7*n+n*(K+2)+6*n*literalRecordBound n L+15 ∧
      Eval prepareFactor k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))⟩ : OuterData) := by
  simpa only [tableResult_incidence] using
    prepareFactor_rel_run s P K n L hn h460 h573 h569 h561 h585 hbody regs


/-- The actual-run table witnesses are dictionaries already specialized to
empty correction support. This is the original-variable lookup format used
by `HashCircuitProgram.Cost.entries`. -/
theorem prepareFactor_good_entries {n B d : ℕ} (s : OuterStore) (u J K L : ℕ)
    (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : RelLiteralBody s literalIteration
      (fun _ bits => ∃ entries : List (MomentsProgram.Product.Entry n B d),
        TruncatedRingProgram.Good ∅ u J entries ∧ bits = MomentsProgram.Product.bytes entries)
      K n L) (regs : Fin 16 → Bool) :
    ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n B d))
      (k : ℕ) (rf : Fin 16 → Bool),
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
      k≤7*n+n*(K+2)+6*n*literalRecordBound n L+15 ∧
      Eval prepareFactor k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ()))⟩ : OuterData) := by
  classical
  obtain ⟨payload,k,rf,hpayload,hk,he⟩ :=
    prepareFactor_rel_lookup s _ K n L hn h460 h573 h569 h561 h585 hbody regs
  have hw (v : Fin n) := (hpayload v.val v.isLt).2
  choose incidence hgood hbytes using hw
  refine ⟨incidence,k,rf,hgood,?_,hk,?_⟩
  · intro v
    rw [← hbytes v]
    exact (hpayload v.val v.isLt).1
  · have hfun : (fun (_ : Unit) (v : Fin n) => MomentsProgram.Product.bytes (incidence v)) =
        (fun (_ : Unit) (v : Fin n) => payload v.val) := by
      funext x v
      exact (hbytes v).symm
    rw [hfun]
    exact he

/-- Clearing only the private worker preserves the selected factor556 and
all caller masters; staging reconstructs every required arithmetic cache. -/
def entryPorts : List (Fin 896) :=
  ((LeafProgram.Incidence.workerPorts.filter (fun i => i ≠ 556)).map basePort) ++
    [62,680,681,682,683,684,881,882]

def initializeWorker : OuterCode := SubexpSetupStorage.clearMany entryPorts

def initialized (a : OuterData) : OuterData := SubexpSetupStorage.clearManyState entryPorts a

theorem initialize_eval (a : OuterData) :
    Eval initializeWorker (SubexpSetupStorage.clearManyCost entryPorts a) a (initialized a) :=
  SubexpSetupStorage.clearMany_eval entryPorts a

theorem initialized_empty (a : OuterData) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) (hne : i ≠ 556) :
    (initialized a).stacks (basePort i) = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨i, List.mem_filter.mpr ⟨(LeafProgram.Incidence.mem_workerPorts i).mpr ⟨hlo,hhi⟩,
    by simpa using hne⟩, rfl⟩

theorem initialized_output (a : OuterData) : (initialized a).stacks 62 = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  exact List.mem_append_right _ (by simp)

theorem initialized_temporary (a : OuterData) : (initialized a).stacks 684 = [] := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_left]
  exact List.mem_append_right _ (by simp)

theorem initialized_selected (a : OuterData) : (initialized a).stacks 556 = a.stacks 556 := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  simp only [entryPorts, List.mem_append]
  rintro (h | h)
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    have hne : i ≠ 556 := by simpa using (List.mem_filter.mp hi).2
    apply hne
    apply basePort_injective
    exact he
  · norm_num [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h

noncomputable def staged (a : OuterData) : OuterData :=
  embedState id basePort (initialized a)
    (LeafProgram.Incidence.staged (projectState id basePort (initialized a)))

def stageCost (a : OuterData) : ℕ :=
  LeafProgram.Incidence.stageCost (projectState id basePort (initialized a)) + 1

theorem stage_eval (a : OuterData) :
    Eval (liftBase LeafProgram.Incidence.stage) (stageCost a) (initialized a) (staged a) := by
  apply eval_liftCommand_from_state _ 0 0 id basePort (initialized a)
    Function.injective_id basePort_injective
  apply LeafProgram.Incidence.stage_eval
  simpa only [projectState, Function.comp_apply,
    show basePort 684 = (684 : Fin 896) from rfl] using initialized_temporary a

noncomputable def exported (a : OuterData) : OuterData :=
  embedState id basePort a (LeafProgram.Incidence.exported (projectState id basePort a))

def exportCost (a : OuterData) : ℕ :=
  LeafProgram.Incidence.exportCost (projectState id basePort a) + 1

theorem export_eval (a : OuterData) (htmp : a.stacks 684 = []) :
    Eval (liftBase LeafProgram.Incidence.exportResult) (exportCost a) a (exported a) := by
  apply eval_liftCommand_from_state _ 0 0 id basePort a
    Function.injective_id basePort_injective
  apply LeafProgram.Incidence.export_eval
  exact htmp

theorem exported_output (a : OuterData) (h62 : a.stacks 62 = []) :
    (exported a).stacks 62 = a.stacks 561 := by
  change (exported a).stacks (basePort 62) = a.stacks 561
  rw [exported, embedState_stack _ _ _ _ basePort_injective]
  exact LeafProgram.Incidence.exported_output _ h62

/-- Exact closed table command, with the old paid staging and export programs
relocated away from all persistent layout masters. -/
def command : OuterCode :=
  .seq initializeWorker (.seq (liftBase LeafProgram.Incidence.stage)
    (.seq prepareFactor (liftBase LeafProgram.Incidence.exportResult)))

/-- Every initialization, staging, table iteration, export and cleanup
instruction belongs to this same fixed program. -/
theorem command_eval (a b : OuterData) (steps : ℕ)
    (he : Eval prepareFactor steps (staged a) b) (htmp : b.stacks 684 = []) :
    Eval command (SubexpSetupStorage.clearManyCost entryPorts a +
      (stageCost a + (steps + exportCost b))) a (exported b) :=
  (initialize_eval a).seq ((stage_eval a).seq (he.seq (export_eval b htmp)))

def program := compiled command 556 62

def callerRegisters (i : Fin 16) : Fin 40 := i.castAdd 24

def caller : Cmd 40 896 := .call (ProgramLinking.liftProgram program callerRegisters id)

/-- The retained pair accumulator is outside every destination of the actual
source, specialization, unary loop, initialization and export instructions. -/
theorem command_not_mem_851 : (851 : Fin 896) ∉ CommandStackFrames.writes command := by
  have hbase (c : Cmd 16 768) : (851 : Fin 896) ∉ CommandStackFrames.writes (liftBase c) :=
    CommandStackFrames.not_mem_liftCommand c 0 0 id basePort 851
      (basePort_outside 851 (Or.inr (by decide)))
  have hinner (c : Code) : (851 : Fin 896) ∉ CommandStackFrames.writes (liftInner c) := by
    apply CommandStackFrames.not_mem_liftCommand c 0 0 id innerPort 851
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=851 at hv
    omega
  have hjoined : (851 : Fin 896) ∉ CommandStackFrames.writes
      (liftCommand QueryProducerSpace.Native.command 205 217 id joinedPort) := by
    apply CommandStackFrames.not_mem_liftCommand _ 205 217 id joinedPort 851
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=851 at hv
    omega
  have hcopy : (851 : Fin 896) ∉ CommandStackFrames.writes
      (SubexpSetupStorage.copyCmd 857 625 881) :=
    CommandStackFrames.not_mem_copyProgram 857 625 881 0 1 851
      (by decide) (by decide) (by decide)
  have hspecialize : (851 : Fin 896) ∉ CommandStackFrames.writes specializeCall :=
    not_mem_union hcopy hjoined
  have hlow : (851 : Fin 896) ∉ CommandStackFrames.writes lowPayload :=
    not_mem_union (hbase _) hspecialize
  have hpayload : (851 : Fin 896) ∉ CommandStackFrames.writes literalPayload :=
    not_mem_union (hinner _) (not_mem_union (hinner _) hlow)
  have hiteration : (851 : Fin 896) ∉ CommandStackFrames.writes literalIteration :=
    not_mem_union (hinner _) (not_mem_union hpayload (hinner _))
  have hloop := CommandStackFrames.not_mem_unaryFor literalPorts literalIteration 851
    (by decide) hiteration
  have hprepare : (851 : Fin 896) ∉ CommandStackFrames.writes prepareFactor :=
    not_mem_union (hinner _) (not_mem_union hloop (hinner _))
  have hentry : (851 : Fin 896) ∉ entryPorts := by
    rw [entryPorts,List.mem_append]
    rintro (hm | hm)
    · obtain ⟨i,_,hi⟩ := List.mem_map.mp hm
      exact basePort_outside 851 (Or.inr (by decide)) ⟨i,hi⟩
    · norm_num [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hm
  have hinitialize := CommandStackFrames.not_mem_clearMany entryPorts 851 hentry
  exact not_mem_union hinitialize
    (not_mem_union (hbase _) (not_mem_union hprepare (hbase _)))

theorem caller_not_mem_851 : (851 : Fin 896) ∉ CommandStackFrames.writes caller := by
  change (851 : Fin 896) ∉ CommandStackFrames.programWrites
    (ProgramLinking.liftProgram program callerRegisters id)
  rw [CommandStackFrames.liftProgram_writes,Finset.image_id]
  exact CommandStackFrames.not_mem_compiled command 556 62 851 command_not_mem_851

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
