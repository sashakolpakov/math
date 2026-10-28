import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoaderCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeContract

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem entry_eq_native : entry=Native.entry := rfl

/-- The actual cache bootstrap is a fixed finite program. -/
def bootstrapProgram := compiled (.seq boot retainCache) 307 647

def bootstrapResult (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) : Data :=
  retainedState (bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)

theorem bootstrapResult_masters (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    MasterFrame (Native.start s a ra rd rc words) (bootstrapResult s a ra rd rc words) := by
  constructor
  intro i hi
  have h660 : i≠660 := by
    intro h; subst i
    exact (by decide : (660 : Fin 768)∉masters) hi
  have h665 : i≠665 := by
    intro h; subst i
    exact (by decide : (665 : Fin 768)∉masters) hi
  simp only [Native.start,nodeStart,tupleInitialized,bootstrapResult,
    Function.update_of_ne h660,Function.update_of_ne h665]

theorem bootstrapResult_length_le_start (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (i : Fin 768) :
    ((bootstrapResult s a ra rd rc words).stacks i).length ≤
      ((Native.start s a ra rd rc words).stacks i).length := by
  by_cases h660 : i=660
  · subst i; simp [Native.start,nodeStart,tupleInitialized,bootstrapResult]; omega
  by_cases h665 : i=665
  · subst i; simp [Native.start,nodeStart,tupleInitialized,bootstrapResult]
  simp [Native.start,nodeStart,tupleInitialized,bootstrapResult,h660,h665]

theorem bootstrapResult_markers (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (bootstrapResult s a ra rd rc words).stacks 660=a.stacks 660 ∧
      (bootstrapResult s a ra rd rc words).stacks 665=a.stacks 665 := by
  constructor
  · rw [bootstrapResult,retainedState_frame _ 660 (by decide) (by decide) (by decide) (by decide)]
    exact bootState_frame a ra rd rc s.r s.node.val s.records s.height (unary s.R)
      s.width words 660 (by decide) (by decide)
  · rw [bootstrapResult,retainedState_frame _ 665 (by decide) (by decide) (by decide) (by decide)]
    exact bootState_frame a ra rd rc s.r s.node.val s.records s.height (unary s.R)
      s.width words 665 (by decide) (by decide)

/-- The cache words used by all subsequent head calls are produced by this
paid run. Its all-stack prefix bound includes the retained cache copies. -/
theorem native_bootstrap_run_space (s : Native.Inputs) (a : Data)
    (ha : Native.Ready s a) (S : ℕ) (hS : WordBound S a) :
    ∃ ra rd rc words steps,
      CacheCorrect s.height (unary s.R) s.width words ∧
      steps ≤ 20000*(S+1)^4+1 ∧
      Trace bootstrapProgram steps (a.withPC (some bootstrapProgram.entry))
        ((bootstrapResult s a ra rd rc words).withPC none) ∧
      WordBound (2*(S+1)^2+3) (bootstrapResult s a ra rd rc words) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ steps →
        Trace bootstrapProgram prefixSteps (a.withPC (some bootstrapProgram.entry)) intermediate →
        dataBits intermediate ≤ 768*S+20000*(S+1)^4+1 := by
  obtain ⟨ra,rd,rc,words,t,ht,he,hlen,hwords,hvalues⟩ :=
    boot_eval a s.r s.node.val s.records s.height (unary s.R) s.width
      ha.colors ha.node (ha.plans.trans s.records_bytes.symm) ha.height ha.order ha.width
      (by simpa [unary] using s.width_boot)
  have hr : s.r ≤ S := by simpa [ha.colors,unary] using hS 130
  have hnode : s.node.val ≤ S := by simpa [ha.node,unary] using hS 307
  have hrecords : (OAI.Algorithms.SubexponentialSAT.Encoding.encodeList id s.records).length ≤ S := by
    simpa [s.records_bytes,ha.plans] using hS 136
  have hheight : s.height.length ≤ S := by simpa [ha.height] using hS 139
  have hR : (unary s.R).length ≤ S := by simpa [ha.order] using hS 138
  have hwidth : s.width.length ≤ S := by simpa [ha.width] using hS 140
  have hb := initializeCost_polynomial a ra rd rc s.r s.node.val s.records s.height
    (unary s.R) s.width words S hS hr hnode hrecords hheight hR hwidth hlen hwords
  let b := bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have htime : t+retainCost b ≤ 20000*(S+1)^4 := by
    have hc := hb.1
    unfold initializeCost at hc
    dsimp [b]
    omega
  have hout : WordBound (2*(S+1)^2+3) (bootstrapResult s a ra rd rc words) :=
    fun i => (bootstrapResult_length_le_start s a ra rd rc words i).trans (hb.2 i)
  refine ⟨ra,rd,rc,words,t+retainCost b+1,⟨hlen,hwords,hvalues⟩,
    Nat.add_le_add_right htime 1,compiled_halt_trace (he.seq (retainCache_eval b)) 307 647,
    hout,?_⟩
  have hin : dataBits (a.withPC (some bootstrapProgram.entry)) ≤ 768*S :=
    StreamResources.dataBits_le_mul _ hS
  intro prefixSteps intermediate hp hpre
  have hg := trace_dataBits bootstrapProgram hpre
  omega

/-- Fresh node caches depend only on fixed source parameters, independently
of the retained caller frame and of the number of previous node calls. -/
def bootstrapOutputBound (s : Native.Inputs) : ℕ :=
  s.Q*s.r+s.r+s.D+s.R*s.width.length+s.width.length+s.height.length+s.R+3

/-- Paid clearing of the three cache destinations permits one fixed maximum
bound at every node boundary. The old tuple markers are never generated. -/
theorem native_bootstrap_retained_bound (s : Native.Inputs) (a : Data)
    (ha : Native.Ready s a) (A : ℕ) (hA : WordBound A a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (h710 : a.stacks 710=[]) (h711 : a.stacks 711=[]) (h712 : a.stacks 712=[]) :
    WordBound (max A (bootstrapOutputBound s)) (bootstrapResult s a ra rd rc words) := by
  let K := max A (bootstrapOutputBound s)
  have hK : bootstrapOutputBound s ≤ K := Nat.le_max_right _ _
  have haK : WordBound K a := fun i => (hA i).trans (Nat.le_max_left _ _)
  have hr : s.r ≤ K := by unfold bootstrapOutputBound at hK; omega
  have ht : s.node.val ≤ K := by simpa [ha.node,unary] using haK 307
  have htr : s.node.val*s.r ≤ K := by
    have h := Nat.mul_le_mul_right s.r s.node.isLt.le
    unfold bootstrapOutputBound at hK
    omega
  have hrecords : (OAI.Algorithms.SubexponentialSAT.Encoding.encodeList id s.records).length ≤ K := by
    simpa [s.records_bytes,ha.plans] using haK 136
  have hD : s.records.length ≤ K := by
    rw [s.records_length]
    unfold bootstrapOutputBound at hK
    omega
  have hh : s.height.length ≤ K := by unfold bootstrapOutputBound at hK; omega
  have hR : (unary s.R).length ≤ K := by
    simp only [unary,List.length_replicate]
    unfold bootstrapOutputBound at hK
    omega
  have hwidth : s.width.length ≤ K := by unfold bootstrapOutputBound at hK; omega
  have hneg : (unary s.R).length*s.width.length ≤ K := by
    simp only [unary,List.length_replicate]
    unfold bootstrapOutputBound at hK
    omega
  have hflat : words.flatten.length ≤ K := by
    rw [cacheWords_flat_length words s.width.length hw.2.1,hw.1]
    exact hneg
  have hden : (LayoutProgram.IntegerCache.denominatorWord (unary s.R).length).length ≤ K := by
    simp only [LayoutProgram.IntegerCache.denominatorWord,List.length_append,
      List.length_replicate,List.length_singleton,unary]
    unfold bootstrapOutputBound at hK
    omega
  let b := bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have hb : WordBound K b := bootState_wordBound a ra rd rc s.r s.node.val s.records
    s.height (unary s.R) s.width words K haK
    (addressResult_wordBound ra s.r s.node.val K hr ht htr)
    (rowCountState_wordBound rd s.records K hrecords hD)
    (cacheState_wordBound rc s.height (unary s.R) s.width words K hh hR hwidth hflat hneg hden)
  have bf (i : Fin 768) (hi : Protected i)
      (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) : b.stacks i=a.stacks i :=
    bootState_frame a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words i hi hne
  have hret : WordBound K (retainedState b) := by
    intro i
    by_cases hp : i=710
    · subst i
      rw [retainedState_positive_append,bf 710 (by decide) (by decide),h710,List.append_nil]
      exact hb 640
    by_cases hn : i=711
    · subst i
      rw [retainedState_negative_append,bf 711 (by decide) (by decide),h711,List.append_nil]
      exact hb 641
    by_cases hd : i=712
    · subst i
      rw [retainedState_denominator_append,bf 712 (by decide) (by decide),h712,List.append_nil]
      exact hb 642
    by_cases htmp : i=659
    · subst i
      simp [retainedState,retainedCopies,copyManyState,copyState,StackRoutines.copyStacks,
        clearMany_stacks,retainedPorts]
    rw [retainedState_frame b i htmp hp hn hd]
    exact hb i
  exact hret

/-- The physical shift word is retained exactly from the source bank. Its
word-length cap can therefore be fixed independently of the caller frame. -/
theorem native_offset_word (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b) :
    b.stacks 141=a.stacks 141 :=
  (hf.stored 141 (by decide)).trans (Native.start_low s a ra rd rc words 141 (by decide))

/-- The signature shift is the actual retained native offset word. -/
theorem native_offset (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b) :
    BinaryArithmetic.toNat (b.stacks 141)=s.offset := by
  rw [hf.stored 141 (by decide),Native.start_low s a ra rd rc words 141 (by decide)]
  exact ha.offset

/-- Readout uses the full signed integer incidence coefficient. The physical
negative word is dominated by W because the native relation bounds both
components together, not merely the absolute difference. -/
theorem native_shifted_integer (s : Native.Inputs) (W : List Bool)
    (hW : BinaryArithmetic.toNat W=s.offset) (j v : ℕ)
    (pair : LayoutMatrixProgram.Pair) (y : List Bool)
    (hp : s.relation j v pair) (hy : BucketProgram.shiftedWord W pair y) :
    (BinaryArithmetic.toNat y : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
      ((LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).map
        (BucketProgram.ProducedRank.entryNat s.packing s.height.length s.R s.node j)).sum := by
  have hmass : RowSelectionProgram.pairTotal pair.1 pair.2 ≤ s.offset := hp.2
  have hneg : BinaryArithmetic.toNat pair.2 ≤ BinaryArithmetic.toNat W := by
    rw [hW]
    unfold RowSelectionProgram.pairTotal at hmass
    omega
  have hshift := BucketProgram.shiftedWord_integer W pair y hy hneg
  have hvalue := hp.1
  change RowSelectionProgram.pairValue pair=_ at hvalue
  change (BinaryArithmetic.toNat y : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
    RowSelectionProgram.pairValue pair at hshift
  rw [hvalue] at hshift
  exact hshift

/-- Each typed physical coefficient is the literal owner-sum entry in the
actual ascending head order. Every original incidence row is retained. -/
theorem native_shiftedMatrix_typed (s : Native.Inputs) (W : List Bool)
    (hW : BinaryArithmetic.toNat W=s.offset)
    (owner : Fin s.D → Fin s.n) (ps : Fin s.D → ℕ × ℕ)
    (hplans : s.plans=List.ofFn ps) (hp : ∀ i,(ps i).1=(owner i).val)
    (z : ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    ∃ c : Fin s.D → Fin (selectedHeads s.n s.rows s.low z).length → List Bool,
      shifted=List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i,(BinaryArithmetic.toNat (c j i) : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
        LayoutProducedMatrix.literalNat s.packing owner s.height.length s.R s.node
          j.val ((selectedHeads s.n s.rows s.low z).get i) := by
  obtain ⟨c,hc,hentry⟩ := shiftedMatrix_typed W s.relation s.columnLength s.D
    (selectedHeads s.n s.rows s.low z) raw shifted hr hy
  refine ⟨c,hc,?_⟩
  intro j i
  obtain ⟨pair,hpair,_,hshift⟩ := hentry j i
  have hv : (selectedHeads s.n s.rows s.low z).get i<s.n :=
    HeadIdentifierProgram.chosenIds_bound _ _ _ (List.get_mem _ _)
  have hvalue := native_shifted_integer s W hW j.val _ pair (c j i) hpair hshift
  rw [hplans] at hvalue
  exact hvalue.trans (congrArg (fun x : ℤ => (BinaryArithmetic.toNat W : ℤ)+x)
    (BucketProgram.ProducedRank.fiber_value_literal s.packing owner s.height.length s.R
      s.node ps hp j ⟨_,hv⟩))

/-- The coarse resource polynomial keeps the complete raw row count and the
actual per-column budget; its degree is independent of the input. -/
def localWork (s : Native.Inputs) (z A : ℕ) : ℕ :=
  let size := Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z
  let matrix := LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n
    (selectedHeads s.n s.rows s.low z)+1
  let live := A+5*size^2+matrix
  let shift := 10000*(s.D+1)*(s.n+1)*(live+s.columnLength+1)^2
  100000*(A+size^3+1)+(matrix+1878*(live+1))+
    (shift+147*(live+shift+1))+(2*(live+shift)+3)

/-- The actual native producer supplies the entry contract for this loader.
Only physical source/cache correctness is required, as obtained from the paid
node bootstrap; there is no matrix evaluator or supplied output table. -/
theorem native_local_eval (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b)
    (z : ℕ) (hz : b.stacks 649=unary z) :
    ∃ rp rm rs raw shifted t,
      t ≤ localBudget b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted
        s.columnTime s.columnLength s.D ∧
      Eval localCommand t b (localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (b.stacks 141))) raw shifted ∧
      (localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks 668=
        Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) ∧
      (localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks 669=[] ∧
      ∀ A,WordBound A b → t ≤ localWork s z A := by
  have hb (i : Fin 768) (hm : i∈masters) (hi : i.val<340) : b.stacks i=a.stacks i :=
    (hf.stored i hm).trans (Native.start_low s a ra rd rc words i hi)
  obtain ⟨rp,tp,htp,hep⟩ := prepareHead_eval b s.n s.N s.rows s.low (s.Q*s.r) z
    ((hb 128 (by decide) (by decide)).trans ha.ambient) ((hb 129 (by decide) (by decide)).trans ha.factors)
    ((hb 134 (by decide) (by decide)).trans ha.low) hz ((hb 133 (by decide) (by decide)).trans ha.words)
    ((hb 132 (by decide) (by decide)).trans ha.wordWidth) s.rows_width s.rows_length
  let p := preparedHead b rp s.n s.N s.rows s.low (s.Q*s.r) z
  have hD : b.stacks 647=unary s.D := by
    rw [hf.stored 647 (by decide)]
    simpa only [Native.start,s.records_length] using
      nodeStart_dimension a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words
  have hp647 : p.stacks 647=unary s.D :=
    (preparedHead_frame b rp s.n s.N s.rows s.low (s.Q*s.r) z 647
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hD
  have hc := entryContract_prepared_master Native.entry _ b hf rp s.n s.N (s.Q*s.r) z s.rows s.low
    s.valid s.relation s.columnTime s.columnLength
    (Native.initial_contract s a ha ra rd rc words hw)
  obtain ⟨rm,raw,tm,hr,htm,hem,hom,hmb⟩ := raw_eval p s.D s.n
    (selectedHeads s.n s.rows s.low z) hp647
    (by simpa [p,LayoutMatrixProgram.ids_eq_indices] using
      preparedHead_ids b rp s.n s.N s.rows s.low (s.Q*s.r) z)
    s.valid s.relation s.columnTime s.columnLength hc
    (by intro j hj v hv; exact ⟨hj,HeadIdentifierProgram.chosenIds_bound _ _ v hv⟩)
    (by intro v hv; exact (HeadIdentifierProgram.chosenIds_bound _ _ v hv).le)
  let m := returned id (by decide) matrixInputs rawOutputs p
    (LayoutMatrixProgram.finalState (matrixBase p) rm raw)
  obtain ⟨rs,shifted,ts,hys,hts,hes,hos,hsb⟩ := shift_eval m raw hom
  let e := returned shiftRegs (by decide) shiftInputs shiftOutputs m
    (BucketProgram.preMatrixState rs (m.stacks 141) []
      (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words)))
  have hm141 : m.stacks 141=b.stacks 141 :=
    (returned_frame id (by decide) matrixInputs rawOutputs p _ 141
      (by decide) (by simp [rawOutputs])).trans
      (preparedHead_frame b rp s.n s.N s.rows s.low (s.Q*s.r) z 141
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨rp,rm,rs,raw,shifted,tp+(tm+(ts+(2*(e.stacks 669).length+3))),
    ?_,hep.seq (hem.seq (hes.seq (clear_eval 669 e))),hr,?_,?_,?_,?_⟩
  · exact Nat.add_le_add htp (Nat.add_le_add htm (Nat.add_le_add_right hts _))
  · simpa only [hm141] using hys
  · simpa only [localResult,clearState,Function.update_of_ne (by decide : (668:Fin 768)≠669)] using hos
  · simp [localResult,clearState]
  · intro A hA
    let size := Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z
    let matrix := LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n
      (selectedHeads s.n s.rows s.low z)+1
    let live := A+5*size^2+matrix
    let shift := 10000*(s.D+1)*(s.n+1)*(live+s.columnLength+1)^2
    have hpB := Bounds.prepareHead_bound b rp s.n s.N s.rows s.low (s.Q*s.r) z A hA
      (by have hh := s.rows_length; omega)
    have hmB := hmb (A+5*size^2) hpB.1
    have hmW : (m.stacks 141).length ≤ live+s.columnLength :=
      (hmB.2 141).trans (Nat.le_add_right _ _)
    have hpairs := raw_pair_bounds hr
    obtain ⟨hrows,hwrows⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
    have hlen := Bounds.selectedHeads_length s.n s.rows s.low z
    have hsB := hsb live (live+s.columnLength) s.n hmB.2 hmW (by
      intro row hrow
      refine ⟨?_,(hwrows row hrow).le.trans hlen⟩
      intro pair hpair
      have hh := hpairs row hrow pair hpair
      exact ⟨hh.1.trans (Nat.le_add_left _ _),hh.2.trans (Nat.le_add_left _ _)⟩)
    rw [hrows] at hsB
    have he669 : (e.stacks 669).length ≤ live+shift := hsB.2 669
    have hpCost : tp ≤ 100000*(A+size^3+1) := htp.trans hpB.2
    change tp+(tm+(ts+(2*(e.stacks 669).length+3))) ≤
      100000*(A+size^3+1)+(matrix+1878*(live+1))+
        (shift+147*(live+shift+1))+(2*(live+shift)+3)
    have hmCost : tm ≤ matrix+1878*(live+1) := hmB.1
    have hsCost : ts ≤ shift+147*(live+shift+1) := hsB.1
    omega

/-- Native correctness, polynomial local work, and all-prefix stack storage
belong to one actual run of the fixed local loader. -/
theorem native_local_run_space (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b)
    (z A : ℕ) (hz : b.stacks 649=unary z)
    (hA : WordBound A b) :
    ∃ rp rm rs raw shifted steps,
      steps ≤ localWork s z A+1 ∧
      Trace localProgram steps (b.withPC (some localProgram.entry))
        ((localResult b rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).withPC none) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (b.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ steps →
        Trace localProgram prefixSteps (b.withPC (some localProgram.entry)) intermediate →
        dataBits intermediate ≤ 768*A+localWork s z A+1 := by
  obtain ⟨rp,rm,rs,raw,shifted,t,_,he,hr,hy,_,_,hb⟩ :=
    native_local_eval s a ha ra rd rc words hw b hf z hz
  have ht := hb A hA
  refine ⟨rp,rm,rs,raw,shifted,t+1,Nat.add_le_add_right ht 1,
    compiled_halt_trace he 649 668,hr,hy,?_⟩
  have hin : dataBits (b.withPC (some localProgram.entry)) ≤ 768*A :=
    StreamResources.dataBits_le_mul _ hA
  intro prefixSteps intermediate hp hpre
  have h := trace_dataBits localProgram hpre
  omega

/-- A complete fixed40-register head reload follows from actual native
bootstrap data. The same halted run has exact full integer rows and both
resource bounds; it does not assume a successful local execution. -/
theorem native_leafFrom_run_space (src : Fin 896) (s : Native.Inputs)
    (a : Data) (ha : Native.Ready s a) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (words : List (List Bool)) (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hf : MasterFrame (Native.start s a ra rd rc words) (projectState leafRegs lowStacks frame))
    (z A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896)))
    (hz : frame.stacks src=unary z)
    (hA : WordBound A frame) :
    ∃ rp rm rs raw shifted total,
      total ≤ 36*A+22*(localWork s z A+1)+35 ∧
      Trace (programFrom src) total (frame.withPC (some (programFrom src).entry))
        ((leafOutputFrom src frame (localResult (leafInputFrom src frame) rp rm rs
          s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)).withPC none) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (programFrom src) prefixSteps (frame.withPC (some (programFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+(localWork s z A+1)+1) := by
  let outer := projectState leafRegs id frame
  let b := leafInputFrom src frame
  have houter : WordBound A outer := hA
  have hb : WordBound A b := fun i =>
    addressStateFrom_wordBound src outer A hs houter (lowStacks i)
  have hbz : b.stacks 649=unary z :=
    (addressStateFrom_value src outer hs).trans hz
  have hb141 : b.stacks 141=frame.stacks 141 :=
    addressStateFrom_frame src outer 141 (by decide)
  obtain ⟨rp,rm,rs,raw,shifted,t,_,he,hr,hy,_,_,hc⟩ := native_local_eval s a ha
    ra rd rc words hw b (leafInputFrom_masters src frame _ hf) z hbz
  have tr := compiled_halt_trace he 649 668
  obtain ⟨total,ht,htr,hprefix⟩ := leafFrom_run_space src frame outer _ (t+1)
    (localWork s z A+1) A hs houter (Nat.add_le_add_right (hc A hb) 1) tr
  have hframe : embedState leafRegs id frame outer=frame :=
    embedState_project leafRegs id frame leafRegs.injective Function.injective_id
  rw [hframe] at htr hprefix
  exact ⟨rp,rm,rs,raw,shifted,total,ht,htr,hr,by simpa only [hb141] using hy,hprefix⟩

/-- Scalar sum used only for a fixed-degree resource envelope. -/
def workSize (s : Native.Inputs) (z A : ℕ) : ℕ :=
  A+Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z+
    s.columnTime+s.columnLength+s.D+s.n+2

private theorem matrixCost_polynomial (T B D n U : ℕ) (js : List ℕ)
    (hjs : ∀ v∈js,v ≤ n) (hT : T ≤ U) (hB : B ≤ U) (hD : D ≤ U)
    (hn : n ≤ U) (hh : js.length ≤ U) (hU : 1 ≤ U) :
    LayoutMatrixProgram.commandCost T B D n js+1 ≤ 1001*U^3 := by
  have hc := LayoutMatrixProgram.commandCost_le_explicit T B D n js hjs
  have hpoly : LayoutMatrixProgram.commandCost T B D n js ≤ 1000*U^3 := by
    apply hc.trans
    calc
      _ ≤ 19*(1+(2*U+2)*U)+12+
        U*(9*U+7*(1+(2*U+2)*U)+U*(U+24*U+8*U+45)+27) := by gcongr
      _ ≤ 1000*U^3 := by
        have h12 : U ≤ U^2 := by nlinarith only [hU]
        have h23 : U^2 ≤ U^3 := pow_le_pow_right₀ hU (by decide)
        nlinarith only [hU,h12,h23]
  have h1 : 1 ≤ U^3 := one_le_pow₀ hU
  omega

private theorem loaderArithmetic_bound (A size matrix B D n U : ℕ)
    (hU : 1 ≤ U) (hA : A ≤ U) (hS : size ≤ U) (hB : B ≤ U)
    (hD : D ≤ U) (hn : n ≤ U) (hm : matrix ≤ 1001*U^3) :
    let live := A+5*size^2+matrix
    let shift := 10000*(D+1)*(n+1)*(live+B+1)^2
    100000*(A+size^3+1)+(matrix+1878*(live+1))+
      (shift+147*(live+shift+1))+(2*(live+shift)+3) ≤ 100000000000000*U^8 := by
  let live := A+5*size^2+matrix
  let shift := 10000*(D+1)*(n+1)*(live+B+1)^2
  have h13 : U ≤ U^3 := by simpa only [pow_one] using pow_le_pow_right₀ hU (by decide : 1 ≤ 3)
  have h23 : U^2 ≤ U^3 := pow_le_pow_right₀ hU (by decide)
  have h38 : U^3 ≤ U^8 := pow_le_pow_right₀ hU (by decide)
  have h18 : 1 ≤ U^8 := one_le_pow₀ hU
  have hs2 : size^2 ≤ U^2 := Nat.pow_le_pow_left hS 2
  have hs3 : size^3 ≤ U^3 := Nat.pow_le_pow_left hS 3
  have hlive : live ≤ 1007*U^3 := by dsimp [live]; omega
  have hw : live+B+1 ≤ 1009*U^3 := by omega
  have hshift : shift ≤ 40723240000*U^8 := by
    calc
      _ ≤ 10000*(2*U)*(2*U)*(1009*U^3)^2 := by
        dsimp only [shift]
        gcongr <;> omega
      _ = 40723240000*U^8 := by ring
  change 100000*(A+size^3+1)+(matrix+1878*(live+1))+
    (shift+147*(live+shift+1))+(2*(live+shift)+3) ≤ 100000000000000*U^8
  omega

/-- One fixed power bounds every concrete preparation, matrix, shift, and
cleanup cost. No input-dependent exponent is introduced. -/
theorem localWork_le_monomial (s : Native.Inputs) (z A : ℕ) :
    localWork s z A ≤ 100000000000000*(workSize s z A)^8 := by
  let U := workSize s z A
  let size := Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z
  let matrix := LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n
    (selectedHeads s.n s.rows s.low z)+1
  have hU : 1 ≤ U := by dsimp [U,workSize]; omega
  have hA : A ≤ U := by dsimp [U,workSize]; omega
  have hS : size ≤ U := by dsimp [U,workSize,size]; omega
  have hT : s.columnTime ≤ U := by dsimp [U,workSize]; omega
  have hB : s.columnLength ≤ U := by dsimp [U,workSize]; omega
  have hD : s.D ≤ U := by dsimp [U,workSize]; omega
  have hn : s.n ≤ U := by dsimp [U,workSize]; omega
  have hm : matrix ≤ 1001*U^3 := matrixCost_polynomial _ _ _ _ _ _
    (fun v hv => (HeadIdentifierProgram.chosenIds_bound _ _ v hv).le)
    hT hB hD hn ((Bounds.selectedHeads_length s.n s.rows s.low z).trans hn) hU
  exact loaderArithmetic_bound A size matrix s.columnLength s.D s.n U hU hA hS hB hD hn hm

/-- The paid address/import/export ABI has the same fixed-degree envelope. -/
theorem leafWork_le_monomial (s : Native.Inputs) (z A : ℕ) :
    36*A+22*(localWork s z A+1)+35 ≤ 10000000000000000*(workSize s z A)^8 := by
  have h := localWork_le_monomial s z A
  have hA : A ≤ workSize s z A := by unfold workSize; omega
  have hU : 1 ≤ workSize s z A := by unfold workSize; omega
  have hpow : workSize s z A ≤ (workSize s z A)^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by decide : 1 ≤ 8)
  have h1 : 1 ≤ (workSize s z A)^8 := one_le_pow₀ hU
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
