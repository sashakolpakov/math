import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeRows

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

/-- The original physical row stage, independent of either old code-search
controller: inputs are the actually retained new search results. -/
def rowInputs : List Route :=
  [(801,3),(782,4),(768,5),(808,6),(809,7),(814,8),(816,9),(815,10),(812,11)]
def rowOutputs : List Route := [(12,777)]
def serialize : Cmd 40 896 :=
  stage rowInputs CodeRowsProgram.program regs16 stacks64 rowOutputs

theorem rowInputs_valid : ∀ p ∈ rowInputs, routeValid p := by
  intro p hp
  simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide

theorem rowOutputs_valid : ∀ p ∈ rowOutputs, routeValid p := by
  intro p hp
  simp only [rowOutputs,List.mem_singleton] at hp
  subst p
  unfold routeValid
  decide

private theorem single_saved {r s : ℕ} (inputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (source dest : Fin 896) (hd : 768 ≤ dest.val) :
    (stageResult inputs [(source,dest)] register stack a out).stacks dest =
      (stageReturned inputs register stack a out).stacks source := by
  rw [stageResult,clearWorker_frame _ dest hd]
  simp [stageSaved,routesState,routed]

/-- Native code construction uses the metadata producer and both streamed
searches before physically serializing their retained matrices. -/
def command : Cmd 40 896 := .seq parameters (.seq NativeCode.searches serialize)

theorem worker_empty (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] := by
  intro i hi
  have h := he ⟨i.val, hi⟩
  simpa [workerStack] using h

/-- Every numeric code dimension is already represented by a physical
unary word at the metadata boundary; its value is bounded by that word cap. -/
theorem metadata_value_bound {m occurrence A : ℕ} (a : Data)
    (hmeta : Metadata m occurrence a) (ha : ∀ i, (a.stacks i).length ≤ A)
    (j : Fin 7) : CodeParametersProgram.parameterValues m occurrence j ≤ A := by
  have h := ha (unaryMetadataPort j)
  rw [hmeta.unary j, List.length_replicate] at h
  exact h

/-- The stored vertex word is nonempty, so a true metadata boundary has a
positive physical bound even in a zero-dimensional code. -/
theorem metadata_bound_pos {m occurrence A : ℕ} (a : Data)
    (hmeta : Metadata m occurrence a) (ha : ∀ i, (a.stacks i).length ≤ A) : 1 ≤ A := by
  have h := metadata_value_bound a hmeta ha 6
  change 2 ^ SparseCode.dimension m occurrence ≤ A at h
  exact (Nat.one_le_pow _ _ (by decide)).trans h

theorem metadata_searches {m occurrence A : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (hmeta : Metadata m occurrence a)
    (ha : ∀ i, (a.stacks i).length ≤ A) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ NativeCode.searchesTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval NativeCode.searches steps a out ∧ out.stacks 816 = CodeSearchProgram.matrixFrames shifts ∧
      out.stacks 815 = CodeSearchProgram.matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ NativeCode.searchBoundary A m occurrence) ∧
      ∀ k c, k ≤ steps → Trace (compiled NativeCode.searches 784 788) k
        (a.withPC (some (compiled NativeCode.searches 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ NativeCode.searchesSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  apply NativeCode.searches_eval hm hocc A a ha (worker_empty a he) hmeta.q
  · exact hmeta.binary 0
  · exact hmeta.unary 0
  · exact hmeta.unary 1
  · exact hmeta.unary 2
  · exact hmeta.unary 3
  · exact hmeta.unary 4
  · have h := hmeta.unary 5
    change a.stacks 813 = List.replicate
      (SparseCode.dimension m occurrence * SparseCode.degree m occurrence) true at h
    simpa only [Nat.mul_comm] using h

theorem serializer_prepared {r D t : ℕ} (a : Data) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true) :
    projectState regs16 stacks64 (routesState rowInputs a) =
      CodeRowsProgram.inputState ((routesState rowInputs a).regs ∘ regs16)
        dword mword width shifts Q := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    have hz : a.stacks (stacks64 i) = [] := hw _ (by simp only [stacks64,Fin.val_castAdd]; omega)
    by_cases h3 : i=3
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h4 : i=4
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h5 : i=5
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h6 : i=6
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h7 : i=7
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h8 : i=8
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h9 : i=9
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h10 : i=10
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h11 : i=11
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    have v3 : i.val≠3 := fun h => h3 (Fin.ext h)
    have v4 : i.val≠4 := fun h => h4 (Fin.ext h)
    have v5 : i.val≠5 := fun h => h5 (Fin.ext h)
    have v6 : i.val≠6 := fun h => h6 (Fin.ext h)
    have v7 : i.val≠7 := fun h => h7 (Fin.ext h)
    have v8 : i.val≠8 := fun h => h8 (Fin.ext h)
    have v9 : i.val≠9 := fun h => h9 (Fin.ext h)
    have v10 : i.val≠10 := fun h => h10 (Fin.ext h)
    have v11 : i.val≠11 := fun h => h11 (Fin.ext h)
    have hf : ∀ p ∈ rowInputs, p.2≠stacks64 i := by
      intro p hp
      simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hv := congrArg Fin.val h <;> simp only [stacks64,Fin.val_castAdd] at hv <;> omega
    change (routesState rowInputs a).stacks (stacks64 i)=_
    rw [routes_frame rowInputs a (stacks64 i) hf,hz]
    simp only [h3,h4,h5,h6,h7,h8,h9,h10,h11,ite_false]

theorem serialize_eval {r D t m : ℕ} (a : Data) (W : ℕ) (hW : WordBound W a)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true)
    (hdv : BinaryArithmetic.toNat dword = D) (hmv : BinaryArithmetic.toNat mword = m)
    (hcap : 3*m ≤ 2^width.length) :
    ∃ steps b, Eval serialize steps a b ∧
      steps ≤ 10000*(W+CodeRowsProgram.cost dword mword width shifts Q+1) ∧
      b.stacks 777 = CodeRowsProgram.rowStream width.length m shifts Q ∧
      (∀ i : Fin 768, b.stacks (workerStack i) = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → b.stacks i = a.stacks i) := by
  have hp := serializer_prepared a dword mword width shifts Q hw hd hm hb hD ht hN hs hQ hr
  obtain ⟨rf,hrun⟩ := CodeRowsProgram.program_runsIn
    ((routesState rowInputs a).regs ∘ regs16) dword mword width shifts Q hdv hmv hcap
  rw [← hp] at hrun
  obtain ⟨steps,hsteps,he⟩ := stage_bounded_eval rowInputs rowOutputs
    CodeRowsProgram.program regs16 stacks64 (Fin.castAdd_injective 16 24)
    (Fin.castAdd_injective 64 832)
    (by intro i h; have hh := congrArg Fin.val h; simp [stacks64] at hh; omega)
    rowInputs_valid rowOutputs_valid (by decide) (by decide) a W hW (hw 767 (by decide))
    _ _ hrun
  let out := CodeRowsProgram.outputState (m:=m) rf dword mword width shifts Q
  refine ⟨steps,stageResult rowInputs rowOutputs regs16 stacks64 a out,he,hsteps,?_,
    stageResult_empty _ _ _ _ _ _,?_⟩
  · rw [show rowOutputs = [(12,777)] from rfl,single_saved _ _ _ _ _ _ _ (by decide)]
    have hh := embedState_stack regs16 stacks64 (routesState rowInputs a) out
      (Fin.castAdd_injective 64 832) 12
    simpa [stageReturned,stacks64,out,CodeRowsProgram.outputState] using hh
  · intro i hi h777
    apply stageResult_frame _ _ _ _ _ _ i hi
    · intro p hp
      simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    · intro p hp
      simp only [rowOutputs,List.mem_singleton] at hp
      subst p
      exact Ne.symm h777
    · intro j h
      have hh := congrArg Fin.val h
      simp only [stacks64,Fin.val_castAdd] at hh
      omega


def serializerTime (r D t W : ℕ) (dword mword width : List Bool) : ℕ :=
  10000 * (W + CodeRowsProgram.explicitCost r D t width.length dword.length mword.length + 1)

/-- Serialization is an actual polynomial-time phase, including its routing
and complete lower-bank cleanup, so instruction growth also bounds its prefix
storage. The preceding searches never use this argument. -/
theorem serializer_trace_space {r D t m : ℕ} (a : Data) (W : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true)
    (hdv : BinaryArithmetic.toNat dword = D) (hmv : BinaryArithmetic.toNat mword = m)
    (hcount : BinaryArithmetic.toNat width = 3*m) :
    ∃ steps b, steps ≤ serializerTime r D t W dword mword width ∧
      Eval serialize steps a b ∧
      b.stacks 777 = CodeRowsProgram.rowStream width.length m shifts Q ∧
      WorkerEmpty b ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + serializerTime r D t W dword mword width) ∧
      ∀ k c, k ≤ steps → Trace (compiled serialize 784 788) k
        (a.withPC (some (compiled serialize 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ W + serializerTime r D t W dword mword width := by
  have hcap := (SubexpParameterProgram.value_lt_two_pow_length width).le
  rw [CounterPrograms.value_eq_toNat, hcount] at hcap
  obtain ⟨steps, b, he, htime, hout, hempty, hframe⟩ := serialize_eval a W ha
    dword mword width shifts Q hblank hd hm hb hD ht hN hs hQ hr hdv hmv hcap
  rw [CodeRowsProgram.cost_eq_explicit] at htime
  change steps ≤ serializerTime r D t W dword mword width at htime
  refine ⟨steps, b, htime, he, hout, hempty, hframe, ?_, ?_⟩
  · exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound ha he) (Nat.add_le_add_left htime W)
  · intro k c hk hc i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le hc i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    omega

theorem serializerTime_polynomial {r D t W S : ℕ} (dword mword width : List Bool)
    (hS : 1 ≤ S) (hW : W ≤ S) (hr : r ≤ S) (hD : D ≤ S) (ht : t ≤ S)
    (hdword : dword.length ≤ S) (hmword : mword.length ≤ S) (hwidth : width.length ≤ S)
    (hvertices : 2^r ≤ 2*S) :
    W + serializerTime r D t W dword mword width ≤ 10000030000 * S^5 := by
  have hcost := SparseCodeProgram.codeRows_explicitCost_le r D t width.length
    dword.length mword.length S hS hr hD ht hwidth hdword hmword hvertices
  have hpow : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have hpos : 1 ≤ S^5 := one_le_pow₀ hS
  unfold serializerTime
  nlinarith


def afterMetadata : Cmd 40 896 := .seq NativeCode.searches serialize

def afterTime (A m occurrence qlen : ℕ) (dword mword width : List Bool) : ℕ :=
  NativeCode.searchesTime A m occurrence qlen dword.length +
    serializerTime (SparseCode.dimension m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.localRows m occurrence) (NativeCode.searchBoundary A m occurrence)
      dword mword width

def afterBoundary (A m occurrence : ℕ) (dword mword width : List Bool) : ℕ :=
  NativeCode.searchBoundary A m occurrence +
    serializerTime (SparseCode.dimension m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.localRows m occurrence) (NativeCode.searchBoundary A m occurrence)
      dword mword width

def afterSpace (A m occurrence qlen : ℕ) (dword mword width : List Bool) : ℕ :=
  max (NativeCode.searchesSpace A m occurrence qlen dword.length)
    (afterBoundary A m occurrence dword mword width)

/-- Concrete metadata words feed both searches and the serializer. The
serializer consumes exactly the matrices returned by those searches. -/
theorem afterMetadata_eval {m occurrence A : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (hmeta : Metadata m occurrence a)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hmword : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hwidth : BinaryArithmetic.toNat (a.stacks 768) = 3*m) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ afterTime A m occurrence (a.stacks 800).length (a.stacks 801) (a.stacks 782) (a.stacks 768) ∧
      Eval afterMetadata steps a out ∧
      out.stacks 777 = CodeRowsProgram.rowStream (a.stacks 768).length m shifts Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      WorkerEmpty out ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → i ≠ 815 → i ≠ 816 →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ afterBoundary A m occurrence
        (a.stacks 801) (a.stacks 782) (a.stacks 768)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterMetadata 784 788) k
        (a.withPC (some (compiled afterMetadata 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ afterSpace A m occurrence (a.stacks 800).length
          (a.stacks 801) (a.stacks 782) (a.stacks 768) := by
  obtain ⟨ns, b, shifts, Q, hns, hes, hshifts, hQ, hgood, hdist, hbempty, hbf, hb, hbs⟩ :=
    metadata_searches hm hocc a he hmeta ha
  have bp (i : Fin 896) (hi : 768 ≤ i.val) (h815 : i ≠ 815) (h816 : i ≠ 816) :
      b.stacks i = a.stacks i := hbf i hi h815 h816
  have hu (j : Fin 7) : b.stacks (unaryMetadataPort j) =
      List.replicate (CodeParametersProgram.parameterValues m occurrence j) true := by
    rw [bp]
    · exact hmeta.unary j
    · simp only [unaryMetadataPort]; omega
    · intro h; have := congrArg Fin.val h; simp only [unaryMetadataPort] at this; have := j.isLt; omega
    · intro h; have := congrArg Fin.val h; simp only [unaryMetadataPort] at this; have := j.isLt; omega
  obtain ⟨nr, out, hnr, her, hout, hempty, hf, hbound, hspace⟩ :=
    serializer_trace_space b (NativeCode.searchBoundary A m occurrence) hb
      (a.stacks 801) (a.stacks 782) (a.stacks 768) shifts Q hbempty
      (bp 801 (by decide) (by decide) (by decide))
      (bp 782 (by decide) (by decide) (by decide))
      (bp 768 (by decide) (by decide) (by decide))
      (hu 0) (hu 1) (hu 6) hshifts hQ (hu 4) (hmeta.binary 0) hmword hwidth
  refine ⟨ns + nr, out, shifts, Q, Nat.add_le_add hns hnr, hes.seq her, hout,
    hgood, hdist, hempty, ?_, hbound, ?_⟩
  · intro i hi h777 h815 h816
    exact (hf i hi h777).trans (hbf i hi h815 h816)
  · exact StructuredSpace.sequence_stack_bound hes her 784 788
      (fun k c hk hc i => (hbs k c hk hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (hspace k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled afterMetadata 784 788) (siteAddress afterMetadata) (exitAddress afterMetadata)
      (compiled_site afterMetadata 784 788)


/-- All physical services in code construction are instantiated. The exposed
intermediate state is the actual metadata-stage result and carries its proved
word cap for the later uniform numerical comparison. -/
theorem command_eval {m occurrence W : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (ha : ∀ i, (a.stacks i).length ≤ W)
    (hmword : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hoccword : BinaryArithmetic.toNat (a.stacks 786) = occurrence)
    (hwidth : BinaryArithmetic.toNat (a.stacks 768) = 3*m) :
    ∃ (steps : ℕ) (prepared out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      let P := NativeLeafSetup.parameterTime m occurrence W (a.stacks 782).length (a.stacks 786).length
      let A := W + P
      steps ≤ P + afterTime A m occurrence (prepared.stacks 800).length
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768) ∧
      Eval command steps a out ∧
      Metadata m occurrence prepared ∧
      (∀ i, (prepared.stacks i).length ≤ A) ∧
      (prepared.stacks 800).length ≤ (a.stacks 782).length + (a.stacks 786).length + 11 ∧
      (prepared.stacks 801).length ≤ 4*(a.stacks 782).length + 2*(a.stacks 786).length + 30 ∧
      out.stacks 777 = CodeRowsProgram.rowStream (a.stacks 768).length m shifts Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      WorkerEmpty out ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → i.val < 800 ∨ 816 < i.val →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ afterBoundary A m occurrence
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768)) ∧
      ∀ k c, k ≤ steps → Trace (compiled command 784 788) k
        (a.withPC (some (compiled command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (A + 1)
          (afterSpace A m occurrence (prepared.stacks 800).length
            (prepared.stacks 801) (a.stacks 782) (a.stacks 768)) := by
  obtain ⟨np, p, hnp, hep, hpempty, _, hmeta, hql, hDl, hpf, hpbound, _, hpspace⟩ :=
    NativeLeafSetup.parameters_trace_space a hm hocc he hmword hoccword ha
  have hp782 : p.stacks 782 = a.stacks 782 := hpf 782 (by decide) (Or.inl (by decide))
  have hp768 : p.stacks 768 = a.stacks 768 := hpf 768 (by decide) (Or.inl (by decide))
  have hpm : BinaryArithmetic.toNat (p.stacks 782) = m := by rw [hp782]; exact hmword
  have hpw : BinaryArithmetic.toNat (p.stacks 768) = 3*m := by rw [hp768]; exact hwidth
  obtain ⟨ns, out, shifts, Q, hns, hes, hrows, hgood, hdist, hempty, hframe, hbound, hspace⟩ :=
    afterMetadata_eval hm hocc p hpempty hmeta hpbound hpm hpw
  simp only [hp782, hp768] at hns hrows hbound hspace
  refine ⟨np + ns, p, out, shifts, Q, Nat.add_le_add hnp hns, hep.seq hes,
    hmeta, hpbound, hql, hDl, hrows, hgood, hdist, hempty, ?_, hbound, ?_⟩
  · intro i hi h777 hrange
    have h815 : i ≠ 815 := by
      intro h; have hv := congrArg Fin.val h
      change i.val = 815 at hv
      omega
    have h816 : i ≠ 816 := by
      intro h; have hv := congrArg Fin.val h
      change i.val = 816 at hv
      omega
    exact (hframe i hi h777 h815 h816).trans (hpf i hi (by omega))
  · exact StructuredSpace.sequence_stack_bound hep hes 784 788
      (fun k c hk hc i => (hpspace k c (Nat.le_succ_of_le hk) hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (hspace k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled command 784 788) (siteAddress command) (exitAddress command)
      (compiled_site command 784 788)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
