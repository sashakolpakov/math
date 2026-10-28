import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeGuard
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeCaches
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def pairScratch : List (Fin 896) :=
  (List.finRange 56).map (Fin.castAdd 840) ++
    (List.finRange 28).map (fun i => (⟨100+i.val,by omega⟩ : Fin 896)) ++ [159,841,848,849]

private theorem low_mem (i : Fin 896) :
    i∈(List.finRange 56).map (Fin.castAdd 840) ↔ i.val<56 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  · intro h
    exact List.mem_map.mpr ⟨⟨i.val,h⟩,List.mem_finRange _,Fin.ext rfl⟩

private theorem normalize_mem (i : Fin 896) :
    i∈(List.finRange 28).map (fun j => (⟨100+j.val,by omega⟩ : Fin 896)) ↔
      100 ≤ i.val ∧ i.val<128 := by
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    have hv := congrArg Fin.val hj
    change 100+j.val=i.val at hv
    omega
  · intro h
    refine List.mem_map.mpr ⟨⟨i.val-100,by omega⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    dsimp
    omega

theorem pairScratch_mem (i : Fin 896) : i∈pairScratch ↔
    i.val<56 ∨ (100 ≤ i.val ∧ i.val<128) ∨ i=159 ∨ i=841 ∨ i=848 ∨ i=849 := by
  simp [pairScratch,low_mem,normalize_mem]

def clearPair : Code := liftCommand (SubexpSetupStorage.clearMany pairScratch) 0 0
  FactorEnvironment.registerMap id

noncomputable def clearPairState (a : Data) : Data :=
  embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a))

def clearPairCost (a : Data) : ℕ :=
  SubexpSetupStorage.clearManyCost pairScratch (projectState FactorEnvironment.registerMap id a)+1

theorem clearPair_eval (a : Data) : Eval clearPair (clearPairCost a) a (clearPairState a) :=
  eval_liftCommand_from_state _ 0 0 FactorEnvironment.registerMap id a
    (Fin.castAdd_injective 16 24) Function.injective_id
    (SubexpSetupStorage.clearMany_eval pairScratch _)

theorem clearPair_stacks (a : Data) (i : Fin 896) :
    (clearPairState a).stacks i = if i∈pairScratch then [] else a.stacks i := by
  unfold clearPairState
  rw [show (embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a))).stacks i =
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a)).stacks i from
        embedState_stack FactorEnvironment.registerMap id a _ Function.injective_id i]
  rw [SubexpSetupStorage.clearMany_stacks]
  rfl

theorem clearPair_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((clearPairState a).stacks i).length≤ B := by
  intro i
  rw [clearPair_stacks]
  split
  · exact Nat.zero_le _
  · exact hb i

theorem clearPair_low (a : Data) (i : Fin 56) :
    (clearPairState a).stacks (FactorEnvironment.lowPort i) = [] := by
  rw [clearPair_stacks,ite_eq_left]
  rw [pairScratch_mem]
  exact Or.inl i.isLt

/-- The signed-update environment is read from persistent actual cache words;
no coefficient table or arithmetic scratch is supplied by an oracle. -/
def pairEnvironment (a : Data) : Squarefree.ScaleProgram.Environment :=
  ⟨a.stacks 194,a.stacks 202,a.stacks 203,a.stacks 201,a.stacks 211,a.stacks 204⟩

def preparePair : Code := .seq clearPair
  (.seq FactorEnvironment.bootstrap (overwrite 211 34))

noncomputable def preparedPair (a : Data) : Data :=
  overwriteState 211 34 (FactorEnvironment.bootstrapResult (clearPairState a))

noncomputable def preparePairCost (a : Data) : ℕ := clearPairCost a+
  (FactorEnvironment.bootstrapCost (clearPairState a)+
    (2*((FactorEnvironment.bootstrapResult (clearPairState a)).stacks 34).length+
      7*((FactorEnvironment.bootstrapResult (clearPairState a)).stacks 211).length+8))

theorem preparePair_eval (a : Data) :
    Eval preparePair (preparePairCost a) a (preparedPair a) := by
  have ht : (clearPairState a).stacks 159=[] := by
    rw [clearPair_stacks,ite_eq_left (by decide : (159 : Fin 896)∈pairScratch)]
  have hcopy : (FactorEnvironment.bootstrapResult (clearPairState a)).stacks 841=[] := by
    rw [FactorEnvironment.bootstrap_frame _ _ (by decide),clearPair_stacks]
    rw [ite_eq_left (by decide : (841 : Fin 896)∈pairScratch)]
  exact (clearPair_eval a).seq ((FactorEnvironment.bootstrap_eval _ ht).seq
    (overwrite_eval 211 34 (by decide) (by decide) (by decide) _ hcopy))

theorem preparedPair_low (a : Data) (i : Fin 40) :
    (preparedPair a).stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle (pairEnvironment a)
        (a.stacks 851) []) i := by
  rw [preparedPair,overwriteState_stacks 211 34 (by decide),FactorEnvironment.bootstrap_stacks]
  fin_cases i <;> simp [leafScalePorts,pairEnvironment,Squarefree.ScaleProgram.tapes,
    Squarefree.ScaleProgram.idle,Squarefree.ScaleProgram.nativeIdle,clearPair_stacks,pairScratch_mem]

theorem preparedPair_normalize (a : Data) : NormalizeScratchReady (preparedPair a) := by
  constructor
  intro i h5 h12 h24 h15 h27
  rw [preparedPair,overwriteState_stacks 211 34 (by decide),FactorEnvironment.bootstrap_stacks]
  fin_cases i <;> simp_all [leafNormalizePorts,clearPair_stacks,pairScratch_mem]

theorem preparedPair_frame (a : Data) (i : Fin 896) (hi : i∉pairScratch) :
    (preparedPair a).stacks i=a.stacks i := by
  have h34 : i≠34 := by
    intro h; subst i; exact hi (by decide)
  have he : i∉FactorEnvironment.environmentPorts := by
    intro h
    simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hi (by decide)
  rw [preparedPair,overwriteState_frame _ _ (by decide) _ _ h34,
    FactorEnvironment.bootstrap_frame _ _ he,clearPair_stacks,ite_eq_right hi]

theorem preparedPair_sign (a : Data) :
    (preparedPair a).stacks 848=[] ∧ (preparedPair a).stacks 849=[] := by
  simp [preparedPair,overwriteState_stacks 211 34 (by decide),
    FactorEnvironment.bootstrap_stacks,clearPair_stacks,pairScratch_mem]

private theorem bootstrapPair_bound (a : Data) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((FactorEnvironment.bootstrapResult (clearPairState a)).stacks i).length≤ B := by
  intro i
  by_cases hi : i∈FactorEnvironment.environmentPorts
  · simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [FactorEnvironment.bootstrap_stacks]
    all_goals simp [clearPair_stacks,pairScratch_mem]
    all_goals exact hb _
  · rw [FactorEnvironment.bootstrap_frame _ _ hi]
    exact clearPair_bound a B hb i

/-- Bootstrap replaces cleared scratch words with existing master words and
therefore restores the same retained bound independently of visit count. -/
theorem preparedPair_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((preparedPair a).stacks i).length≤ B :=
  overwriteState_bound 211 34 (by decide) _ B (bootstrapPair_bound a B hb)

theorem clearPairCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    clearPairCost a ≤ 176*B+265 := by
  have h := SubexpSetupStorage.clearManyCost_le pairScratch
    (projectState FactorEnvironment.registerMap id a) B hb
  have hl : pairScratch.length=88 := by simp [pairScratch]
  rw [hl] at h
  unfold clearPairCost
  omega

theorem preparePairCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    preparePairCost a ≤ 50000*(B+1) := by
  have hc := clearPairCost_le a B hb
  have hbclear := clearPair_bound a B hb
  have hsum : stackBits (clearPairState a).stacks ≤ 896*B := by
    exact StreamResources.dataBits_le_mul ((clearPairState a).withPC (none : Option (Fin 1))) hbclear
  have hboot := FactorEnvironment.bootstrapCost_le (clearPairState a)
  have hbboot := bootstrapPair_bound a B hb
  have h34 := hbboot 34
  have h211 := hbboot 211
  unfold preparePairCost
  omega

/-- Actual scratch clearing and cache construction are included in this run.
The transient bound is separate from the unchanged retained boundary. -/
theorem preparePair_run_space (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    let p := compiled preparePair 851 850
    Trace p (preparePairCost a+1) (a.withPC (some p.entry)) ((preparedPair a).withPC none) ∧
      preparePairCost a+1≤50001*(B+1) ∧
      (∀ i,((preparedPair a).stacks i).length≤ B) ∧
      ∀ prefixSteps intermediate,prefixSteps≤ preparePairCost a+1 →
        Trace p prefixSteps (a.withPC (some p.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤896*B+50001*(B+1) := by
  dsimp only
  have ht := preparePairCost_le a B hb
  refine ⟨compiled_halt_trace (preparePair_eval a) 851 850,by omega,preparedPair_bound a B hb,?_⟩
  have hin : dataBits (a.withPC (some (compiled preparePair 851 850).entry))≤896*B :=
    StreamResources.dataBits_le_mul _ hb
  intro prefixSteps intermediate hp htrace i
  exact StructuredSpace.local_stack_bound (compiled preparePair 851 850)
    (steps:=50001*(B+1)) hin prefixSteps intermediate (by omega) htrace i

/-- The node accumulator consumes each completed pair dictionary immediately.
The finishing clear restores the same arithmetic workspace for the next pair. -/
def commitPair : Code := .seq preparePair (.seq pairUpdate clearPair)

def commitPairProgram := compiled commitPair 851 850

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram

/-- An actual signed pair commit from physical retained cache words. Good
empty-support storage and the semantic accumulator describe the same entries.
The caller boundary remains B; the polynomial transient is not iterated. -/
theorem commitPair_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ)
    (henv : pairEnvironment a = Squarefree.ScaleProgram.environment p t M cache table minusOne degree width)
    (hpair : a.stacks 851=Product.bytes source) (hnode : a.stacks 850=Product.bytes seed)
    (hb : ∀ i,(a.stacks i).length≤ B)
    (hcapacity : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2)≤ B) :
    let sign := parity (a.stacks 835) (parity (a.stacks 834) false)
    let result := signedSum p t M cache table minusOne sign source seed
    ∃ steps b, Eval commitPair steps a b ∧ Good ∅ u J result ∧
      b.stacks 850=Product.bytes result ∧ b.stacks 851=[] ∧
      (∀ i,i∉pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤ B) ∧
      steps+1≤51000*(B+1)+pairUpdateBudget n (baseWidth p t) d u J
        (a.stacks 834).length (a.stacks 835).length ∧
      Trace commitPairProgram (steps+1) (a.withPC (some commitPairProgram.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps≤ steps+1 →
        Trace commitPairProgram prefixSteps (a.withPC (some commitPairProgram.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤896*B+51000*(B+1)+
          pairUpdateBudget n (baseWidth p t) d u J (a.stacks 834).length (a.stacks 835).length := by
  dsimp only
  let c := preparedPair a
  let e := Squarefree.ScaleProgram.environment p t M cache table minusOne degree width
  let sign := parity (a.stacks 835) (parity (a.stacks 834) false)
  let scaled := signedEntries p t M cache table minusOne sign source
  let result := signedSum p t M cache table minusOne sign source seed
  have hE : c.stacks 834=a.stacks 834 := preparedPair_frame a 834 (by decide)
  have hU : c.stacks 835=a.stacks 835 := preparedPair_frame a 835 (by decide)
  have hs : ∀ i : Fin 40,c.stacks (leafScalePorts (Fin.castAdd 1 i)) =
      Squarefree.ScaleProgram.tapes (Squarefree.ScaleProgram.idle e (Product.bytes source) []) i := by
    intro i
    rw [preparedPair_low,henv,hpair]
  have ha : c.stacks 850=Product.bytes seed :=
    (preparedPair_frame a 850 (by decide)).trans hnode
  obtain ⟨nt,rr,ss,hcost,he,hgood⟩ := pairUpdate_eval p t M cache hz table minusOne source seed
    hsource hseed degree width hd hw c hs (preparedPair_normalize a) ha
    (preparedPair_sign a).1 (preparedPair_sign a).2
  rw [hE,hU] at hcost he hgood
  let b := pairUpdateResult (accumulateLeafResult (pairCallResult c) e rr ss
    (Product.bytes scaled) (Product.bytes result) sign)
  have h850 : b.stacks 850=Product.bytes result := pairUpdateResult_accumulator _ _ _ _ _ _ _
  have h851 : b.stacks 851=[] := by
    simp only [b,pairUpdateResult,Function.update_of_ne (by decide : (851 : Fin 896) ≠ 848)]
    apply accumulateLeafResult_consumed _ _ _ _ _ (Product.bytes seed) _ _
      (pairCallResult_normalizeScratch c (preparedPair_normalize a))
    rw [pairCallResult_stack_frame _ _ (by decide)]
    exact ha
  have hframe (i : Fin 896) (h850 : i≠850) (h851 : i≠851) : b.stacks i=c.stacks i := by
    have hf := pairUpdateResult_frame c e rr ss (Product.bytes source) (Product.bytes scaled)
      (Product.bytes seed) (Product.bytes result) hs (preparedPair_normalize a) ha
      (preparedPair_sign a).1 i h850 h851
    simpa only [hE,hU] using hf
  have hbb : ∀ i,(b.stacks i).length≤ B := by
    intro i
    by_cases hi : i=850
    · subst i
      rw [h850]
      exact (empty_bytes_length_le hgood).trans hcapacity
    by_cases hi' : i=851
    · subst i
      rw [h851]
      exact Nat.zero_le _
    rw [hframe i hi hi']
    exact preparedPair_bound a B hb i
  have hc := clearPair_eval b
  have hex : Eval commitPair (preparePairCost a+(nt+clearPairCost b)) a (clearPairState b) :=
    (preparePair_eval a).seq (he.seq hc)
  have htotal : preparePairCost a+(nt+clearPairCost b)+1 ≤
      51000*(B+1)+pairUpdateBudget n (baseWidth p t) d u J
        (a.stacks 834).length (a.stacks 835).length := by
    have hp := preparePairCost_le a B hb
    have hclear := clearPairCost_le b B hbb
    omega
  refine ⟨_,clearPairState b,hex,hgood,?_,?_,?_,clearPair_bound b B hbb,htotal,
    compiled_halt_trace hex 851 850,?_⟩
  · rw [clearPair_stacks,ite_eq_right (by decide : (850 : Fin 896)∉pairScratch)]
    exact h850
  · rw [clearPair_stacks,ite_eq_right (by decide : (851 : Fin 896)∉pairScratch)]
    exact h851
  · intro i hi hi850 hi851
    rw [clearPair_stacks,ite_eq_right hi,hframe i hi850 hi851,preparedPair_frame a i hi]
  · have hin : dataBits (a.withPC (some commitPairProgram.entry))≤896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hle htrace i
    have hx := StructuredSpace.local_stack_bound commitPairProgram hin
      prefixSteps intermediate (hle.trans htotal) htrace i
    simpa only [Nat.add_assoc] using hx


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes

abbrev LowData := State 40 768

def lowPort : Fin 768 → Fin 896 := Fin.castAdd 128

def low (a : Data) : LowData := projectState id lowPort a

noncomputable def installed (a : Data) (b : LowData) : Data :=
  embedState id lowPort a b

def call (c : Cmd 40 768) : Code := liftCommand c 301 78 id lowPort

theorem call_eval (c : Cmd 40 768) (a : Data) (b : LowData) (steps : ℕ)
    (he : Eval c steps (low a) b) :
    Eval (call c) (steps+1) a (installed a b) :=
  eval_liftCommand_from_state c 301 78 id lowPort a Function.injective_id
    (Fin.castAdd_injective 768 128) he

theorem installed_low (a : Data) (b : LowData) (i : Fin 768) :
    (installed a b).stacks (lowPort i)=b.stacks i :=
  embedState_stack id lowPort a b (Fin.castAdd_injective 768 128) i

theorem installed_high (a : Data) (b : LowData) (i : Fin 896) (hi : 768 ≤ i.val) :
    (installed a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

def initializedLow (a : Data) : LowData :=
  let s := RingNodeSetup.storeOf (low a)
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state (readRegs a.regs 0 1 none)
    (RingNodeSetup.initialized s)

def initializeNodes : Code := .seq (call RingNodeSetup.initNodes)
  (NodeReadoutSpace.clearMany [850,851,863])

noncomputable def initialized (a : Data) : Data :=
  NodeReadoutSpace.clearedMany [850,851,863] (installed a (initializedLow a))

noncomputable def initializeCost (a : Data) : ℕ :=
  RingNodeSetup.initializeCost (RingNodeSetup.storeOf (low a))+1+
    NodeReadoutSpace.clearCost [850,851,863] (installed a (initializedLow a))

theorem initialize_eval (a : Data) :
    Eval initializeNodes (initializeCost a) a (initialized a) := by
  have he := RingNodeSetup.initialize_eval (low a).regs (RingNodeSetup.storeOf (low a))
  rw [RingNodeSetup.state_storeOf] at he
  exact (call_eval _ a _ _ he).seq (NodeReadoutSpace.clearMany_eval _ _)

theorem initializedLow_frame (a : Data) (i : Fin 768)
    (h301 : i≠301) (h302 : i≠302) (h305 : i≠305) (h307 : i≠307) (h78 : i≠78) :
    (initializedLow a).stacks i=(low a).stacks i := by
  have hs := congrArg (fun x : LowData => x.stacks i) (RingNodeSetup.state_storeOf (low a))
  rw [←hs]
  simp only [initializedLow, OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
    RingNodeSetup.initialized, OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes,
    h301,h302,h305,h307,h78,ite_false]

theorem initialized_frame (a : Data) (i : Fin 896)
    (hi : i∉[301,302,305,307,78,850,851,863]) :
    (initialized a).stacks i=a.stacks i := by
  have hn : i∉[850,851,863] := by simp_all
  rw [initialized,NodeReadoutSpace.clearedMany_stack,ite_eq_right hn]
  by_cases hlow : i.val<768
  · let j : Fin 768 := ⟨i.val,hlow⟩
    have hj : lowPort j=i := Fin.ext rfl
    rw [←hj,installed_low,initializedLow_frame]
    · rfl
    all_goals intro h; have hh := congrArg lowPort h; rw [hj] at hh; exact hi (by simp [hh,lowPort])
  · exact installed_high a _ i (by omega)

theorem initialized_words (a : Data) :
    (initialized a).stacks 301=a.stacks 300 ∧
    (initialized a).stacks 302=[] ∧ (initialized a).stacks 305=[] ∧
    (initialized a).stacks 307=[] ∧ (initialized a).stacks 78=[] ∧
    (initialized a).stacks 850=[] ∧ (initialized a).stacks 851=[] ∧
    (initialized a).stacks 863=[] := by
  have hlo (i : Fin 896) (hi : i.val<768) : (installed a (initializedLow a)).stacks i=
      (initializedLow a).stacks ⟨i.val,hi⟩ := by
    have hh : lowPort ⟨i.val,hi⟩=i := Fin.ext rfl
    simpa only [hh] using installed_low a (initializedLow a) ⟨i.val,hi⟩
  simp only [initialized,NodeReadoutSpace.clearedMany_stack]
  simp only [List.mem_cons,Fin.reduceEq,or_self,or_false,ite_true,ite_false,
    List.not_mem_nil,or_true]
  rw [hlo 301 (by decide),hlo 302 (by decide),hlo 305 (by decide),
    hlo 307 (by decide),hlo 78 (by decide)]
  simp [initializedLow,RingNodeSetup.initialized,RingNodeSetup.storeOf,
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes,
    low,projectState,lowPort]


theorem initialized_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((initialized a).stacks i).length≤ B := by
  intro i
  by_cases hi : i∈[301,302,305,307,78,850,851,863]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [(initialized_words a).1,(initialized_words a).2.1,
      (initialized_words a).2.2.1,(initialized_words a).2.2.2.1,
      (initialized_words a).2.2.2.2.1,(initialized_words a).2.2.2.2.2.1,
      (initialized_words a).2.2.2.2.2.2.1,(initialized_words a).2.2.2.2.2.2.2,
      List.length_nil]
    all_goals first | exact hb 300 | exact Nat.zero_le _
  · rw [initialized_frame a i hi]
    exact hb i

theorem initializeCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    initializeCost a≤23*B+30 := by
  have hclear : NodeReadoutSpace.clearCost [850,851,863] (installed a (initializedLow a))≤6*B+9 := by
    simp only [NodeReadoutSpace.clearCost,NodeReadoutSpace.cleared]
    simp only [Function.update_of_ne (by decide : (851 : Fin 896)≠850),
      Function.update_of_ne (by decide : (863 : Fin 896)≠851),
      Function.update_of_ne (by decide : (863 : Fin 896)≠850)]
    rw [installed_high a _ 850 (by decide),installed_high a _ 851 (by decide),
      installed_high a _ 863 (by decide)]
    have := hb 850; have := hb 851; have := hb 863
    omega
  have h301 := hb 301; have h302 := hb 302; have h305 := hb 305
  have h307 := hb 307; have h78 := hb 78; have h300 := hb 300
  unfold initializeCost RingNodeSetup.initializeCost RingNodeSetup.storeOf low projectState at *
  simp only [lowPort] at *
  change 2*((a.stacks 301).length+(a.stacks 302).length+(a.stacks 305).length+
      (a.stacks 307).length+(a.stacks 78).length)+7*(a.stacks 300).length+20+1+
      NodeReadoutSpace.clearCost [850,851,863] (installed a (initializedLow a))≤23*B+30
  omega

theorem initialize_run_space (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    let p := compiled initializeNodes 300 863
    Trace p (initializeCost a+1) (a.withPC (some p.entry)) ((initialized a).withPC none) ∧
      initializeCost a+1≤23*B+31 ∧ (∀ i,((initialized a).stacks i).length≤ B) ∧
      ∀ q z,q≤ initializeCost a+1 → Trace p q (a.withPC (some p.entry)) z →
        ∀ i,(z.stacks i).length≤919*B+31 := by
  dsimp only
  have ht := initializeCost_le a B hb
  refine ⟨compiled_halt_trace (initialize_eval a) 300 863,by omega,initialized_bound a B hb,?_⟩
  intro q z hq he i
  have hi : dataBits (a.withPC (some (compiled initializeNodes 300 863).entry))≤896*B :=
    StreamResources.dataBits_le_mul _ hb
  have hx := StructuredSpace.local_stack_bound (compiled initializeNodes 300 863)
    (steps:=23*B+31) hi q z (by omega) he i
  omega

/-- Actual reset before each node. The old tuple markers and retained integer
cache destinations are cleared so repeated bootstrap copies cannot accumulate. -/
def nodeResetPorts : List (Fin 896) := [78,302,660,665,710,711,712,850,851]

def beginNode : Code := .seq (NodeReadoutSpace.clearMany nodeResetPorts)
  (call RingNodeSetup.readNode)

def clearedNode (a : Data) : Data := NodeReadoutSpace.clearedMany nodeResetPorts a

def readLow (a : Data) (bits : List Bool) (tail : List (List Bool)) : LowData :=
  let c := low (clearedNode a)
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state (RingNodeSetup.nodeRegs c.regs)
    (RingNodeSetup.nodeRead (RingNodeSetup.storeOf c) bits tail)

noncomputable def begunNode (a : Data) (bits : List Bool) (tail : List (List Bool)) : Data :=
  installed (clearedNode a) (readLow a bits tail)

def beginNodeCost (a : Data) (bits : List Bool) : ℕ :=
  NodeReadoutSpace.clearCost nodeResetPorts a+9*bits.length+9

theorem beginNode_eval (a : Data) (bits : List Bool) (tail : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id (bits::tail)) :
    Eval beginNode (beginNodeCost a bits) a (begunNode a bits tail) := by
  let c := low (clearedNode a)
  have hsource : (RingNodeSetup.storeOf c).source=Encoding.encodeList id (bits::tail) := by
    simpa [c,RingNodeSetup.storeOf,low,projectState,lowPort,clearedNode,
      NodeReadoutSpace.clearedMany_stack,nodeResetPorts] using hc
  have hp : (RingNodeSetup.storeOf c).payload=[] := by
    simp [c,RingNodeSetup.storeOf,low,projectState,lowPort,clearedNode,
      NodeReadoutSpace.clearedMany_stack,nodeResetPorts]
  have hn : (RingNodeSetup.storeOf c).node=[] := by
    simp [c,RingNodeSetup.storeOf,low,projectState,lowPort,clearedNode,
      NodeReadoutSpace.clearedMany_stack,nodeResetPorts]
  have hr := RingNodeSetup.readNode_eval c.regs (RingNodeSetup.storeOf c) bits tail hsource hp hn
  rw [RingNodeSetup.state_storeOf] at hr
  have he := (NodeReadoutSpace.clearMany_eval nodeResetPorts a).seq
    (call_eval _ (clearedNode a) (readLow a bits tail) _ hr)
  convert he using 1
  · rfl
  · unfold beginNodeCost
    omega
  · rfl

theorem readLow_frame (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 768) (h301 : i≠301) (h302 : i≠302) (h78 : i≠78) :
    (readLow a bits tail).stacks i=(low (clearedNode a)).stacks i := by
  have hs := congrArg (fun x : LowData => x.stacks i)
    (RingNodeSetup.state_storeOf (low (clearedNode a)))
  change OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes
    (RingNodeSetup.nodeRead (RingNodeSetup.storeOf (low (clearedNode a))) bits tail) i = _
  rw [RingNodeSetup.nodeRead_frame _ _ _ i h301 h302 h78]
  exact hs

theorem begunNode_frame (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i∉301::nodeResetPorts) :
    (begunNode a bits tail).stacks i=a.stacks i := by
  have hc : i∉nodeResetPorts := by simp_all
  have hread : (begunNode a bits tail).stacks i=(clearedNode a).stacks i := by
    by_cases hlo : i.val<768
    · let j : Fin 768 := ⟨i.val,hlo⟩
      have hj : lowPort j=i := Fin.ext rfl
      change (installed (clearedNode a) (readLow a bits tail)).stacks i=_
      rw [←hj,installed_low,readLow_frame]
      · rfl
      all_goals intro h; have hh := congrArg lowPort h; rw [hj] at hh
      all_goals exact hi (by simp [hh,lowPort,nodeResetPorts])
    · exact installed_high _ _ i (by omega)
  rw [hread,clearedNode,NodeReadoutSpace.clearedMany_stack,ite_eq_right hc]



theorem installed_at (a : Data) (b : LowData) (i : Fin 896) (hi : i.val<768) :
    (installed a b).stacks i=b.stacks ⟨i.val,hi⟩ := by
  have hh : lowPort ⟨i.val,hi⟩=i := Fin.ext rfl
  simpa only [hh] using installed_low a b ⟨i.val,hi⟩

theorem readLow_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 768) :
    (readLow a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=302 then [] else
        if i=78 then bits else (low (clearedNode a)).stacks i := by
  by_cases h301 : i=301
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h302 : i=302
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h78 : i=78
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  simp only [h301,h302,h78,ite_false]
  exact readLow_frame a bits tail i h301 h302 h78

theorem begunNode_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 896) :
    (begunNode a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=78 then bits else
        if i∈nodeResetPorts then [] else a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : lowPort j=i := Fin.ext rfl
    have h301 : (j=301) ↔ (i=301) := by simp [j,Fin.ext_iff]
    have h302 : (j=302) ↔ (i=302) := by simp [j,Fin.ext_iff]
    have h78 : (j=78) ↔ (i=78) := by simp [j,Fin.ext_iff]
    rw [begunNode,installed_at _ _ i hlo]
    change (readLow a bits tail).stacks j=_
    rw [readLow_stacks]
    simp only [h301,h302,h78]
    change (if i=301 then Encoding.encodeList id tail else if i=302 then [] else
      if i=78 then bits else (clearedNode a).stacks (lowPort j))=_
    rw [hj,clearedNode,NodeReadoutSpace.clearedMany_stack]
    by_cases h : i=302
    · simp [h,nodeResetPorts]
    · simp only [h,ite_false]
  · have hh := installed_high (clearedNode a) (readLow a bits tail) i (by omega)
    rw [begunNode,hh,clearedNode,NodeReadoutSpace.clearedMany_stack]
    have h301 : i≠301 := by intro h; subst i; exact hlo (by decide)
    have h78 : i≠78 := by intro h; subst i; exact hlo (by decide)
    simp [h301,h78]

theorem begunNode_bound (a : Data) (bits : List Bool) (tail : List (List Bool)) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length ≤ B) (hbits : bits.length ≤ B)
    (htail : (Encoding.encodeList id tail).length ≤ B) :
    ∀ i,((begunNode a bits tail).stacks i).length ≤ B := by
  intro i
  rw [begunNode_stacks]
  split_ifs
  · exact htail
  · exact hbits
  · exact Nat.zero_le _
  · exact hb i

theorem beginNodeCost_le (a : Data) (bits : List Bool) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length ≤ B) (hbits : bits.length ≤ B) :
    beginNodeCost a bits ≤ 27*B+36 := by
  have hc := NodeReadoutSpace.clearCost_le nodeResetPorts a B hb
  have hl : nodeResetPorts.length=9 := rfl
  rw [hl] at hc
  unfold beginNodeCost
  omega

theorem beginNode_run_space (a : Data) (bits : List Bool) (tail : List (List Bool)) (B : ℕ)
    (hc : a.stacks 301=Encoding.encodeList id (bits::tail))
    (hb : ∀ i,(a.stacks i).length ≤ B) (hbits : bits.length ≤ B)
    (htail : (Encoding.encodeList id tail).length ≤ B) :
    let p := compiled beginNode 301 78
    Trace p (beginNodeCost a bits+1) (a.withPC (some p.entry)) ((begunNode a bits tail).withPC none) ∧
      beginNodeCost a bits+1 ≤ 27*B+37 ∧
      (∀ i,((begunNode a bits tail).stacks i).length ≤ B) ∧
      ∀ q z,q ≤ beginNodeCost a bits+1 → Trace p q (a.withPC (some p.entry)) z →
        ∀ i,(z.stacks i).length ≤ 923*B+37 := by
  dsimp only
  have ht := beginNodeCost_le a bits B hb hbits
  refine ⟨compiled_halt_trace (beginNode_eval a bits tail hc) 301 78,by omega,
    begunNode_bound a bits tail B hb hbits htail,?_⟩
  intro q z hq he i
  have hi : dataBits (a.withPC (some (compiled beginNode 301 78).entry)) ≤ 896*B :=
    StreamResources.dataBits_le_mul _ hb
  have hx := StructuredSpace.local_stack_bound (compiled beginNode 301 78)
    (steps:=27*B+37) hi q z (by omega) he i
  omega


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/
namespace TupleMultiply

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram

def ports (i : Fin 768) : Fin 896 :=
  if i=67 then 853 else if i=151 then 852 else i.castAdd 128

theorem ports_injective : Function.Injective ports := by
  have small (i : Fin 768) (h67 : i≠67) (h151 : i≠151) : (ports i).val<768 := by
    simpa only [ports,h67,h151,ite_false,Fin.val_castAdd] using i.isLt
  intro i j hij
  by_cases hi67 : i=67
  · subst i
    by_cases hj67 : j=67
    · exact hj67.symm
    by_cases hj151 : j=151
    · subst j
      exact False.elim ((by decide : (853 : Fin 896)≠852) hij)
    have hj := small j hj67 hj151
    have hv := congrArg Fin.val hij
    change 853=(ports j).val at hv
    omega
  by_cases hi151 : i=151
  · subst i
    by_cases hj67 : j=67
    · subst j
      exact False.elim ((by decide : (852 : Fin 896)≠853) hij)
    by_cases hj151 : j=151
    · exact hj151.symm
    have hj := small j hj67 hj151
    have hv := congrArg Fin.val hij
    change 852=(ports j).val at hv
    omega
  have hi := small i hi67 hi151
  by_cases hj67 : j=67
  · subst j
    have hv := congrArg Fin.val hij
    change (ports i).val=853 at hv
    omega
  by_cases hj151 : j=151
  · subst j
    have hv := congrArg Fin.val hij
    change (ports i).val=852 at hv
    omega
  simp only [ports,hi67,hi151,hj67,hj151,ite_false] at hij
  exact Fin.castAdd_injective 768 128 hij

def raw (a : Data) : Data := NodeReadoutSpace.clearedMany [61,70] a

noncomputable def prepared (a : Data) : Data :=
  FactorEnvironment.bootstrapResult (clearPairState (raw a))

def environment (a : Data) : Product.Store :=
  Product.idle (a.stacks 194) (a.stacks 202) (a.stacks 203) (a.stacks 201)
    (a.stacks 204) (a.stacks 212) (a.stacks 243)

def prepare : Code := .seq (NodeReadoutSpace.clearMany [61,70])
  (.seq clearPair FactorEnvironment.bootstrap)

noncomputable def prepareCost (a : Data) : ℕ :=
  NodeReadoutSpace.clearCost [61,70] a+(clearPairCost (raw a)+
    FactorEnvironment.bootstrapCost (clearPairState (raw a)))

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) := by
  have ht : (clearPairState (raw a)).stacks 159=[] := by
    rw [clearPair_stacks,ite_eq_left (by decide : (159 : Fin 896)∈pairScratch)]
  have he := (NodeReadoutSpace.clearMany_eval [61,70] a).seq
    ((clearPair_eval (raw a)).seq (FactorEnvironment.bootstrap_eval _ ht))
  exact he

theorem prepared_low (a : Data) (i : Fin 56) :
    (prepared a).stacks (FactorEnvironment.lowPort i)=Product.tapes (environment a) i := by
  have h := FactorEnvironment.bootstrap_low (clearPairState (raw a)) (clearPair_low (raw a)) i
  simpa [prepared,environment,clearPair_stacks,pairScratch_mem,raw,
    NodeReadoutSpace.clearedMany_stack] using h

theorem ports_low (i : Fin 56) :
    ports (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i))=
      FactorEnvironment.lowPort i := by
  have h67 : Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)≠67 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=67 at hv
    omega
  have h151 : Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)≠151 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=151 at hv
    omega
  simp only [ports,h67,h151,ite_false]
  rfl

theorem prepared_ready (a : Data) :
    Factor.lowReady (projectState id ports (prepared a)) (environment a) := by
  intro i
  change (prepared a).stacks (ports (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)))=_
  rw [ports_low]
  exact prepared_low a i

theorem prepared_scratch (a : Data) :
    (prepared a).stacks 61=[] ∧ (prepared a).stacks 70=[] ∧ (prepared a).stacks 159=[] := by
  simp [prepared,FactorEnvironment.bootstrap_stacks,clearPair_stacks,pairScratch_mem,
    raw,NodeReadoutSpace.clearedMany_stack]

theorem prepared_frame (a : Data) (i : Fin 896)
    (hp : i∉pairScratch) (h61 : i≠61) (h70 : i≠70) :
    (prepared a).stacks i=a.stacks i := by
  have he : i∉FactorEnvironment.environmentPorts := by
    intro hi
    simp only [FactorEnvironment.environmentPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hp (by decide)
  rw [prepared,FactorEnvironment.bootstrap_frame _ i he,clearPair_stacks,ite_eq_right hp,
    raw,NodeReadoutSpace.clearedMany_stack,ite_eq_right (by simp [h61,h70])]

theorem raw_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B) :
    ∀ i,((raw a).stacks i).length ≤ B := by
  intro i
  rw [raw,NodeReadoutSpace.clearedMany_stack]
  split
  · exact Nat.zero_le _
  · exact hb i

theorem prepared_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B) :
    ∀ i,((prepared a).stacks i).length ≤ B :=
  bootstrapPair_bound (raw a) B (raw_bound a B hb)

def multiply : Code := liftCommand Factor.accumulate 67 151 id ports

noncomputable def productState (a : Data) (b : Factor.Data) : Data := embedState id ports a b

theorem multiply_eval (a : Data) (b : Factor.Data) (steps : ℕ)
    (he : Eval Factor.accumulate steps (projectState id ports a) b) :
    Eval multiply (steps+1) a (productState a b) :=
  eval_liftCommand_from_state _ 67 151 id ports a Function.injective_id ports_injective he

theorem productState_stacks (a : Data) (b : Factor.Data) (word : List Bool)
    (hb : b.stacks=Function.update (Function.update (projectState id ports a).stacks 67 []) 151 word) :
    (productState a b).stacks=Function.update (Function.update a.stacks 853 []) 852 word := by
  funext i
  by_cases hi : ∃ j,ports j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [productState,embedState_stack id ports a b ports_injective j,hb]
    by_cases h67 : j=67
    · subst j
      simp [ports]
    by_cases h151 : j=151
    · subst j
      simp [ports]
    have h853 : ports j≠853 := by
      intro h
      have : ports j=ports 67 := h
      exact h67 (ports_injective this)
    have h852 : ports j≠852 := by
      intro h
      have : ports j=ports 151 := h
      exact h151 (ports_injective this)
    simp [h67,h151,h853,h852,projectState]
  · have h853 : i≠853 := by intro h; subst i; exact hi ⟨67,rfl⟩
    have h852 : i≠852 := by intro h; subst i; exact hi ⟨151,rfl⟩
    rw [productState,embedState_stack_frame id ports a b i hi]
    simp [h853,h852]

theorem prepareCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B) :
    prepareCost a ≤ 50000*(B+1) := by
  have hc := NodeReadoutSpace.clearCost_le [61,70] a B hb
  have hp := clearPairCost_le (raw a) B (raw_bound a B hb)
  have hs : stackBits (clearPairState (raw a)).stacks ≤ 896*B :=
    StreamResources.dataBits_le_mul ((clearPairState (raw a)).withPC (none : Option (Fin 1)))
      (clearPair_bound (raw a) B (raw_bound a B hb))
  have ht := FactorEnvironment.bootstrapCost_le (clearPairState (raw a))
  simp only [List.length_cons,List.length_nil] at hc
  unfold prepareCost
  omega

/-- Consume the current head sum into the tuple product and reclaim the
arithmetic workspace. The input/retained dictionaries have empty formal support. -/
def command : Code := .seq prepare (.seq multiply clearPair)

def program := compiled command 853 852

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d u J : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (seed head : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J seed) (hh : Good ∅ u J head) (a : Data) (B : ℕ)
    (henv : environment a=Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true))
    (hseed : a.stacks 852=Product.bytes seed) (hhead : a.stacks 853=Product.bytes head)
    (hb : ∀ i,(a.stacks i).length ≤ B)
    (hcapacity : FactorProductSpace.byteBound n (baseWidth p t) d u J ≤ B) :
    let result := Product.run p t M cache table u J seed head []
    ∃ steps b, Eval command steps a b ∧ Good ∅ u J result ∧
      b.stacks 852=Product.bytes result ∧ b.stacks 853=[] ∧
      (∀ i,i∉pairScratch → i≠61 → i≠70 → i≠852 → i≠853 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length ≤ B) ∧
      steps+1 ≤ 51000*(B+1)+FactorProductSpace.budget n (baseWidth p t) d u J ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ q z,q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+51000*(B+1)+
          FactorProductSpace.budget n (baseWidth p t) d u J := by
  dsimp only
  let c := prepared a
  have hlo := prepared_ready a
  rw [henv] at hlo
  have hseed' : (projectState id ports c).stacks 151=Product.bytes seed := by
    change c.stacks 852=Product.bytes seed
    rw [prepared_frame a 852 (by decide) (by decide) (by decide)]
    exact hseed
  have hhead' : (projectState id ports c).stacks 67=Product.bytes head := by
    change c.stacks 853=Product.bytes head
    rw [prepared_frame a 853 (by decide) (by decide) (by decide)]
    exact hhead
  have h61 : (projectState id ports c).stacks 61=[] := (prepared_scratch a).1
  have h70 : (projectState id ports c).stacks 70=[] := (prepared_scratch a).2.1
  have h159 : (projectState id ports c).stacks 159=[] := (prepared_scratch a).2.2
  obtain ⟨nt,b,hnt,hgood,he,hbstacks,hbytes,_,_⟩ :=
    FactorProductSpace.accumulate_run_space p t M cache hz table degree width hd hw u J
      seed head hs hh (projectState id ports c) hlo hseed' hhead' h61 h70 h159
  let r := productState c b
  have hr : r.stacks=Function.update (Function.update c.stacks 853 []) 852
      (Product.bytes (Product.run p t M cache table u J seed head [])) :=
    productState_stacks c b _ hbstacks
  have hrbound : ∀ i,(r.stacks i).length ≤ B := by
    intro i
    rw [hr]
    by_cases hi : i=852
    · subst i
      simpa using hbytes.trans hcapacity
    by_cases hi' : i=853
    · subst i
      simp
    simpa [Function.update_of_ne hi,Function.update_of_ne hi'] using prepared_bound a B hb i
  have hrun : Eval command (prepareCost a+((nt+1)+clearPairCost r)) a (clearPairState r) :=
    (prepare_eval a).seq ((multiply_eval c b nt he).seq (clearPair_eval r))
  have ht : prepareCost a+((nt+1)+clearPairCost r)+1 ≤
      51000*(B+1)+FactorProductSpace.budget n (baseWidth p t) d u J := by
    have hp := prepareCost_le a B hb
    have hc := clearPairCost_le r B hrbound
    omega
  refine ⟨_,clearPairState r,hrun,hgood,?_,?_,?_,clearPair_bound r B hrbound,ht,
    compiled_halt_trace hrun 853 852,?_⟩
  · rw [clearPair_stacks,ite_eq_right (by decide : (852 : Fin 896)∉pairScratch),hr]
    simp
  · rw [clearPair_stacks,ite_eq_right (by decide : (853 : Fin 896)∉pairScratch),hr]
    simp
  · intro i hi h61i h70i h852i h853i
    rw [clearPair_stacks,ite_eq_right hi,hr,Function.update_of_ne h852i,
      Function.update_of_ne h853i]
    exact prepared_frame a i hi h61i h70i
  · intro q z hq hz' i
    have hentry : dataBits (a.withPC (some program.entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    have hlocal := StructuredSpace.local_stack_bound program hentry q z (hq.trans ht) hz' i
    simpa only [Nat.add_assoc] using hlocal

end TupleMultiply

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
