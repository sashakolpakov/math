import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramOutputSize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceNativeCost
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

/-! The concrete layout source-row producer, with exact serialized output size.
The producer executes selected packing metadata and ring caches; it takes no
semantic source-row evaluator or precomputed row table as an input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutProgram

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

theorem source_rows_trace {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (s : Store) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
      (p.R+1) (d*baseWidth 3 p.t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s (p.R+1) (d*baseWidth 3 p.t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (hwork : RowWorkClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (howner : ∀ i : Fin 11, (2 : ℕ)  ≤  i.val →
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (ownerStacks i)=[])
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 p.t p.modulus p.cache
      (HornerProgram.modelTable p.t p.model p.modulus p.cache) (s ∘ executorPorts) width frame)
    (E : LayoutSourceRowsProgramReadiness.Empty s)
    (hready : SourceBank.Ready p (⟨fun _ => false,
      clearedSourceStore (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) ∘ sourcePorts⟩ : SourceBank.Data))
    (hsourceClean : ∀ j∈SourceBank.cleanupPorts,
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)=[])
    (hmeta : s 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hsize : ∀ j : Fin 320,
      ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hD : ps.length ≤ S) (hQ : Q ≤ S) (hR : p.R ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (regs : Fin 16 → Bool) :
    ∃ rows steps rf,
      RowProperty DensePolynomialProgram.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out =
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      rows.length = N ∧
      (Encoding.encodeList DensePolynomialProgram.encode rows).length =
        N * (2 * ((p.R+1)*(d*baseWidth 3 p.t)) + 2) + 1 ∧
      steps  ≤  nativeRowsBudget p s v N f S ps + 1 ∧
      Trace sourceRowsProgram steps
        ((⟨regs,s⟩ : Data).withPC (some sourceRowsProgram.entry))
        ((⟨rf,Function.update (initializeFinish s (p.R+1) (d*baseWidth 3 p.t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data).withPC none) := by
  obtain ⟨rows,n,rf,hrows,hlen,hn,he⟩ := sourceRows_run p ps P s v N f S width frame
    hinit hv hN hf hplan hlookup hclean hwork howner H E hready hsourceClean
    hmeta hsize hmetadata hD hQ hR hW hRW regs
  refine ⟨rows,n+1,rf,hrows,hlen,?_,by omega,compiled_halt_trace he 337 205⟩
  rw [RowProperty.serialized_length _ _ _ _ _ hrows, hlen]


/-- Construct the actual raw signed incidence matrix, stopping before the old
materialized bucket controller. The entry contract is discharged by the native
integer-entry and owner-fiber programs, rather than assumed from a caller. -/
theorem native_matrix_runsIn (s : LeafHeadSetupProgram.Native.Inputs)
    (a : LeafHeadSetupProgram.Data) (ha : LeafHeadSetupProgram.Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (js : List ℕ) (hjs : ∀ v ∈ js, v < s.n)
    (hids : (LeafHeadSetupProgram.Native.start s a ra rd rc words).stacks 650 =
      LayoutMatrixProgram.ids js) (regs : Fin 16 → Bool) :
    let base := LeafHeadSetupProgram.matrixBase
      (LeafHeadSetupProgram.Native.start s a ra rd rc words)
    ∃ rf rows,
      RunsIn (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry)
        (LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n js + 1)
        ((LayoutMatrixProgram.initialState base regs s.D).withPC
          (some (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry).entry))
        ((LayoutMatrixProgram.finalState base rf rows).withPC none) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D js rows := by
  dsimp only
  apply LayoutMatrixProgram.program_runsIn LeafHeadSetupProgram.Native.entry
  · simp [LeafHeadSetupProgram.matrixBase]
  · simp [LeafHeadSetupProgram.matrixBase]
  · exact LeafHeadSetupProgram.Native.initial_contract s a ha ra rd rc words hw
  · simpa [LeafHeadSetupProgram.matrixBase] using hids
  · intro j hj v hv
    exact ⟨hj,hjs v hv⟩
  · intro v hv
    exact (hjs v hv).le

/-- The fixed head-selection table reads one unary head address and returns
its original-coordinate IDs, mask, and factor context in their dedicated tapes. -/
def prepareHeadProgram := compiled LeafHeadSetupProgram.prepareHead 649 650

/-- Source generation reads the retained incidence plan and returns all
source rows on545; the caller reads every output bit, independently of the
compiler's chosen Boolean result convention. -/
def sourceCallProgram := compiled LeafProgram.Source.command 136 545

/-- A matrix reload uses the actual node caches and metadata, even after other
heads have run. The only frame condition is equality of the preserved physical
cache tapes; no entry evaluator or matrix is supplied. -/
theorem prepared_native_matrix_runsIn (s : LeafHeadSetupProgram.Native.Inputs)
    (a : LeafHeadSetupProgram.Data) (ha : LeafHeadSetupProgram.Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (b : LeafHeadSetupProgram.Data)
    (hf : LeafHeadSetupProgram.LoopFrame
      (LeafHeadSetupProgram.Native.start s a ra rd rc words) b)
    (rp : Fin 8 → Bool) (z : ℕ) (regs : Fin 16 → Bool) :
    let js := LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z
    let base := LeafHeadSetupProgram.matrixBase
      (LeafHeadSetupProgram.preparedHead b rp s.n s.N s.rows s.low (s.Q*s.r) z)
    ∃ rf rows,
      RunsIn (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry)
        (LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n js + 1)
        ((LayoutMatrixProgram.initialState base regs s.D).withPC
          (some (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry).entry))
        ((LayoutMatrixProgram.finalState base rf rows).withPC none) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D js rows := by
  dsimp only
  apply LayoutMatrixProgram.program_runsIn LeafHeadSetupProgram.Native.entry
  · simp [LeafHeadSetupProgram.matrixBase]
  · simp [LeafHeadSetupProgram.matrixBase]
  · exact LeafHeadSetupProgram.entryContract_prepared _ _ b hf rp s.n s.N
      (s.Q*s.r) z s.rows s.low s.valid s.relation s.columnTime s.columnLength
      (LeafHeadSetupProgram.Native.initial_contract s a ha ra rd rc words hw)
  · simpa [LeafHeadSetupProgram.matrixBase, LayoutMatrixProgram.ids_eq_indices] using
      LeafHeadSetupProgram.preparedHead_ids b rp s.n s.N s.rows s.low (s.Q*s.r) z
  · intro j hj v hv
    exact ⟨hj,HeadIdentifierProgram.chosenIds_bound _ _ v hv⟩
  · intro v hv
    exact (HeadIdentifierProgram.chosenIds_bound _ _ v hv).le

/-- The concrete nonnegative shift preserves the full integer coefficient.
The mass bound comes from the actual native owner-fiber relation, so neither
component can underflow when the negative word is subtracted. -/
theorem native_pair_shifted_integer (s : LeafHeadSetupProgram.Native.Inputs)
    (W : List Bool) (hW : BinaryArithmetic.toNat W=s.offset)
    (j v : ℕ) (p : LayoutMatrixProgram.Pair) (y : List Bool)
    (hp : s.relation j v p) (hy : BucketProgram.shiftedWord W p y) :
    (BinaryArithmetic.toNat y : ℤ) = (BinaryArithmetic.toNat W : ℤ)+
      ((LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).map
        (BucketProgram.ProducedRank.entryNat s.packing s.height.length s.R s.node j)).sum := by
  have hmass : RowSelectionProgram.pairTotal p.1 p.2 ≤ s.offset := hp.2
  have hneg : BinaryArithmetic.toNat p.2 ≤ BinaryArithmetic.toNat W := by
    rw [hW]
    unfold RowSelectionProgram.pairTotal at hmass
    omega
  have hshift := BucketProgram.shiftedWord_integer W p y hy hneg
  have hvalue := hp.1
  change RowSelectionProgram.pairValue p=_ at hvalue
  change (BinaryArithmetic.toNat y : ℤ) = (BinaryArithmetic.toNat W : ℤ)+
    RowSelectionProgram.pairValue p at hshift
  rw [hvalue] at hshift
  exact hshift

/-- The existing 768-stack producer occupies only the low part of the leaf
bank. Streaming pair, tuple, and sign controls above it are caller-owned. -/
def packingLeafStacks : Fin 768 ↪ Fin 896 := Fin.castAddEmb 128

def packingGlobalStacks : Fin 768 ↪ Fin 1220 := packingLeafStacks.trans ABI.leafStacks

def packingLeafProgram :=
  ProgramLinking.liftProgram PackingCallerProgram.program id packingLeafStacks

def packingGlobalProgram :=
  ProgramLinking.liftProgram PackingCallerProgram.program ABI.leafRegisters packingGlobalStacks

theorem packingLeaf_frame (frame : State 40 896) (a : State 40 768)
    (i : Fin 896) (hi : 768 ≤ i.val) :
    (embedState id packingLeafStacks frame a).stacks i=frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

theorem packingLeafCall_eval (frame : State 40 896) {a b : State 40 768} {steps : ℕ}
    (h : Trace PackingCallerProgram.program steps
      (a.withPC (some PackingCallerProgram.program.entry)) (b.withPC none)) :
    Eval (.call packingLeafProgram) steps
      (embedState id packingLeafStacks frame a) (embedState id packingLeafStacks frame b) ∧
    ∀ i : Fin 896,768 ≤ i.val →
      (embedState id packingLeafStacks frame b).stacks i=frame.stacks i := by
  exact ⟨eval_call_lifted PackingCallerProgram.program id packingLeafStacks frame
    Function.injective_id packingLeafStacks.injective h,fun i hi=>packingLeaf_frame frame b i hi⟩

theorem packingGlobalCall_eval (frame : State 80 1220) {a b : State 40 768} {steps : ℕ}
    (h : Trace PackingCallerProgram.program steps
      (a.withPC (some PackingCallerProgram.program.entry)) (b.withPC none)) :
    Eval (.call packingGlobalProgram) steps
      (embedState ABI.leafRegisters packingGlobalStacks frame a)
      (embedState ABI.leafRegisters packingGlobalStacks frame b) :=
  eval_call_lifted PackingCallerProgram.program ABI.leafRegisters packingGlobalStacks frame
    ABI.leafRegisters.injective packingGlobalStacks.injective h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutProgram
