import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoadCommand
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

private theorem eval_loadHead_of_trace
    (p : Program 40 896 (StructuredCalls.size (SignatureHeadLoader.commandFrom headAddress) + 1))
    (hp : SignatureHeadLoader.programFrom headAddress = p)
    {steps : ℕ} {a b : State 40 896}
    (h : Trace p steps (a.withPC (some p.entry)) (b.withPC none)) :
    Eval loadHead steps a b := by
  have hc : loadHead = .call (SignatureHeadLoader.programFrom headAddress) := rfl
  have hcp : loadHead = .call p :=
    hc.trans (congrArg (fun q => Cmd.call q) hp)
  rw [hcp]
  exact .call p h

/-- The physical result of that one concrete head loader. -/
def result (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    State 40 896 :=
  SignatureHeadLoader.leafOutputFrom headAddress frame
    (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom headAddress frame)
      rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)

theorem result_high_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
    (result s z frame rp rm rs raw shifted).stacks i=frame.stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id i).trans
    (SignatureHeadLoader.lowResultFrom_frame headAddress _ _ i hi hne)

theorem result_register_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (result s z frame rp rm rs raw shifted).regs i=frame.regs i :=
  SignatureHeadLoader.leafOutputFrom_registers headAddress frame _ i hi

theorem result_low (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom headAddress frame)
        rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id (SignatureHeadLoader.lowStacks i)).trans
    (SignatureHeadLoader.lowResultFrom_low headAddress _ _ i h659 h668 h669)

theorem result_offset (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 141=frame.stacks 141 := by
  rw [show (141 : Fin 896)=SignatureHeadLoader.lowStacks 141 from rfl,
    result_low s z frame rp rm rs raw shifted 141 (by decide) (by decide) (by decide)]
  rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ 141
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact SignatureHeadLoader.addressStateFrom_frame headAddress _ 141 (by decide)

theorem result_headsize (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 651=
      List.replicate (selectedHeads s.n s.rows s.low z).length false := by
  exact (SignatureHeadLoader.leafFrom_head_outputs headAddress frame _ _ rp rm rs
    s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).2.1

theorem result_matrix (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 847=
      Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) := by
  rw [result, SignatureHeadLoader.leafOutputFrom_matrix]
  exact SignatureHeadLoader.localResult_matrixWord ..

theorem result_raw_empty (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 846=[] :=
  SignatureHeadLoader.leafOutputFrom_raw_empty headAddress frame _

/-- Every local rescan scratch word is blank after actual matrix staging. -/
theorem result_rescan_scratch (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 24) (h0 : i≠0) (h15 : i≠15) (h16 : i≠16) (h17 : i≠17)
    (h18 : i≠18) (_h22 : i≠22) :
    (result s z frame rp rm rs raw shifted).stacks (rescanStacks i)=[] := by
  have hoff : rescanStacks i=SignatureHeadLoader.lowStacks
      (workPort (by decide) (⟨i.val, by omega⟩ : Fin 288)) := by
    fin_cases i <;> first | contradiction | rfl
  have hne (q : Fin 768) (hq : 628 ≤ q.val) :
      workPort (by decide) (⟨i.val, by omega⟩ : Fin 288)≠q := by
    intro he
    have hv := congrArg Fin.val he
    change 340+i.val=q.val at hv
    have := i.isLt
    omega
  rw [hoff, result_low s z frame rp rm rs raw shifted _
    (hne 659 (by decide)) (hne 668 (by decide)) (hne 669 (by decide))]
  exact SignatureHeadLoader.localResult_work_empty ..

/-- The source words and caches retain their exact values across the loader. -/
theorem result_masters (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (base : Data)
    (hf : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (result s z frame rp rm rs raw shifted)) := by
  apply SignatureHeadLoader.leafOutputFrom_masters
  exact (SignatureHeadLoader.leafInputFrom_masters headAddress frame base hf).trans
    (SignatureHeadLoader.localResult_masters ..)

/-- The retained bound is restored exactly; the transient loader envelope is
never fed into the next boundary bound. -/
theorem result_wordBound (s : Native.Inputs) (z F L : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hf : WordBound F frame) (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted) :
    WordBound F (result s z frame rp rm rs raw shifted) := by
  have hin := SignatureHeadLoader.leafInputFrom_wordBound headAddress frame F (by decide) hf
  have hw : (SignatureHeadLoader.leafInputFrom headAddress frame).stacks 141=frame.stacks 141 :=
    SignatureHeadLoader.addressStateFrom_frame headAddress _ 141 (by decide)
  have hb := SignatureHeadLoader.localResult_retained_bound
    (SignatureHeadLoader.leafInputFrom headAddress frame) rp rm rs s.n s.N (s.Q*s.r) z F s.D
    s.columnLength L s.rows s.low raw shifted s.relation hin (by simpa only [hw] using hW)
    hr (by simpa only [hw] using hy)
  rw [Nat.max_eq_left hout] at hb
  exact SignatureHeadLoader.leafOutputFrom_wordBound headAddress frame _ F F
    (by decide) le_rfl hf hb

/-- The complete loader run is obtained from actual native inputs and paid
cache values. No successful matrix execution is an input to this theorem. -/
theorem load_run (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame))
    (z F L : ℕ) (hz : frame.stacks headAddress=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval loadHead total frame (result s z frame rp rm rs raw shifted) ∧
      total≤36*F+22*(SignatureHeadLoader.localWork s z F+1)+35 ∧
      WordBound F (result s z frame rp rm rs raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total →
        Trace (SignatureHeadLoader.programFrom headAddress) prefixSteps
          (frame.withPC (some (SignatureHeadLoader.programFrom headAddress).entry)) intermediate →
        dataBits intermediate≤1000*(F+(SignatureHeadLoader.localWork s z F+1)+1) := by
  obtain ⟨rp,rm,rs,raw,shifted,total,ht,htr,hr,hy,hprefix⟩ :=
    SignatureHeadLoader.native_leafFrom_run_space headAddress s a ha ra rd rc words hw frame hm
      z F (by decide) hz hf
  refine ⟨rp, rm, rs, raw, shifted, total, ?_, ht, ?_, hr, hy, hprefix⟩
  · have hpack : ∃ output,
        output = result s z frame rp rm rs raw shifted ∧
        Trace (SignatureHeadLoader.programFrom headAddress) total
          (frame.withPC (some (SignatureHeadLoader.programFrom headAddress).entry))
          (output.withPC none) := by
      refine ⟨_, ?_, htr⟩
      rw [result]
    obtain ⟨_, rfl, hresult⟩ := hpack
    generalize hp : SignatureHeadLoader.programFrom headAddress = p at hresult
    exact eval_loadHead_of_trace p hp hresult
  · exact result_wordBound s z F L frame rp rm rs raw shifted hf hW hout hr hy

/-- The physically emitted full integer matrix initializes the actual
predecessor scanner at its zero candidate, including empty heads. -/
theorem result_reset_ready (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hc : frame.stacks (tupleStacks 2)=[]) (hk : frame.stacks (tupleStacks 3)=[])
    (hp : frame.stacks (tupleStacks 4)=[]) (hz : frame.stacks (tupleStacks 8)=[]) :
    CandidateReady (resetGeneratorState (result s z frame rp rm rs raw shifted))
      (frame.stacks 141) shifted (selectedHeads s.n s.rows s.low z).length
      ⟨0, Nat.pow_pos (by decide)⟩ := by
  apply reset_candidate_ready
  · exact result_offset ..
  · exact result_matrix ..
  · exact result_headsize ..
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 2)
      (by decide) (by decide)).trans hc
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 3)
      (by decide) (by decide)).trans hk
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 4)
      (by decide) (by decide)).trans hp
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 8)
      (by decide) (by decide)).trans hz
  · exact result_rescan_scratch s z frame rp rm rs raw shifted


/-- All raw incidence rows are present in the scanner, with polynomial
coefficient word lengths. No coordinate grid is materialized. -/
theorem shifted_rows_bounds (s : Native.Inputs) (z L : ℕ) (W : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hW : W.length≤L)
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    shifted.length=s.D ∧
      (∀ row∈shifted, row.length=(selectedHeads s.n s.rows s.low z).length) ∧
      ∀ row∈shifted, ∀ x∈row, x.length≤3*(s.columnLength+L)+1 := by
  obtain ⟨c,hc,hentry⟩ := SignatureHeadLoader.shiftedMatrix_typed W s.relation
    s.columnLength s.D (selectedHeads s.n s.rows s.low z) raw shifted hr hy
  subst shifted
  refine ⟨by simp, ?_, ?_⟩
  · intro row hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    simp
  · intro row hrow x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨pair,_,hpair,hshift⟩ := hentry j i
    have hlength := hshift.2
    unfold LayoutMatrixProgram.pairLength at hpair
    omega

/-- This is the literal signed owner-sum matrix, with every ambient head
coordinate retained in the actual ascending identifier order. -/
def integerMatrix (s : Native.Inputs) (owner : Fin s.D → Fin s.n) (z : ℕ) :
    Fin s.D → Fin (selectedHeads s.n s.rows s.low z).length → ℤ :=
  fun j i => LayoutProducedMatrix.literalNat s.packing owner s.height.length s.R s.node
    j.val ((selectedHeads s.n s.rows s.low z).get i)

/-- Equality of the physically generated whole keys is exactly equality of
full integer signatures. Candidate indices are unchanged. -/
theorem shifted_key_kernel (s : Native.Inputs) (W : List Bool)
    (hW : BinaryArithmetic.toNat W=s.offset)
    (owner : Fin s.D → Fin s.n) (ps : Fin s.D → ℕ × ℕ)
    (hplans : s.plans=List.ofFn ps) (hp : ∀ i,(ps i).1=(owner i).val)
    (z : ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted)
    (i j : Fin (2^(selectedHeads s.n s.rows s.low z).length)) :
    AttainedSignatureProgram.Rescan.naturalKey W shifted
        (selectedHeads s.n s.rows s.low z).length i=
      AttainedSignatureProgram.Rescan.naturalKey W shifted
        (selectedHeads s.n s.rows s.low z).length j ↔
      AttainedSignatures.integerKey (integerMatrix s owner z) i=
        AttainedSignatures.integerKey (integerMatrix s owner z) j := by
  obtain ⟨c,hc,hentry⟩ := SignatureHeadLoader.native_shiftedMatrix_typed s W hW
    owner ps hplans hp z raw shifted hr hy
  rw [hc]
  exact AttainedSignatureProgram.Rescan.naturalKey_eq_iff W c (integerMatrix s owner z) hentry i j


/-- The fixed retained output envelope also pays the extra leading bit of
an exact power-of-two remaining-assignment word. -/
theorem retainedOutputBound_headroom (n N D B L : ℕ) :
    n+1≤SignatureHeadLoader.retainedOutputBound n N D B L := by
  have hn : n≤n*(2*n+2) := by
    calc
      n=n*1 := (Nat.mul_one _).symm
      _≤n*(2*n+2) := Nat.mul_le_mul_left n (by omega)
  unfold SignatureHeadLoader.retainedOutputBound
  omega

/-- A fresh head is loaded and initialized by actual finite commands. The
same run establishes scanner readiness and retains the original bound F. -/
theorem load_reset_run (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame))
    (z F L : ℕ) (hz : frame.stacks headAddress=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hc : frame.stacks (tupleStacks 2)=[]) (hk : frame.stacks (tupleStacks 3)=[])
    (hp : frame.stacks (tupleStacks 4)=[]) (ht : frame.stacks (tupleStacks 5)=[])
    (hrm : frame.stacks (tupleStacks 7)=[]) (hzr : frame.stacks (tupleStacks 8)=[]) :
    ∃ rp rm rs raw shifted total,
      Eval (.seq loadHead resetGeneratorCommand) total frame
        (resetGeneratorState (result s z frame rp rm rs raw shifted)) ∧
      total+1≤61*F+22*(SignatureHeadLoader.localWork s z F+1)+58 ∧
      WordBound F (resetGeneratorState (result s z frame rp rm rs raw shifted)) ∧
      CandidateReady (resetGeneratorState (result s z frame rp rm rs raw shifted))
        (frame.stacks 141) shifted (selectedHeads s.n s.rows s.low z).length
        ⟨0, Nat.pow_pos (by decide)⟩ ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (.seq loadHead resetGeneratorCommand) 0 0) prefixSteps
          (frame.withPC (some (compiled (.seq loadHead resetGeneratorCommand) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤2000*(F+SignatureHeadLoader.localWork s z F+1) := by
  obtain ⟨rp,rm,rs,raw,shifted,t,he,hcost,hbound,hraw,hshift,_⟩ :=
    load_run s a ha ra rd rc words hw frame hm z F L hz hf hW hout
  let b := result s z frame rp rm rs raw shifted
  have hs := result_headsize s z frame rp rm rs raw shifted
  have high (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      b.stacks i=frame.stacks i := result_high_frame s z frame rp rm rs raw shifted i hi hne
  have hb2 : b.stacks (tupleStacks 2)=[] := (high _ (by decide) (by decide)).trans hc
  have hb4 : b.stacks (tupleStacks 4)=[] := (high _ (by decide) (by decide)).trans hp
  have hb5 : b.stacks (tupleStacks 5)=[] := (high _ (by decide) (by decide)).trans ht
  have hb7 : b.stacks (tupleStacks 7)=[] := (high _ (by decide) (by decide)).trans hrm
  have hb8 : b.stacks (tupleStacks 8)=[] := (high _ (by decide) (by decide)).trans hzr
  have hwidth : (selectedHeads s.n s.rows s.low z).length+1≤F :=
    (Nat.add_le_add_right (Bounds.selectedHeads_length s.n s.rows s.low z) 1).trans
      ((retainedOutputBound_headroom s.n s.N s.D s.columnLength L).trans hout)
  have hreset := resetGenerator_eval b (selectedHeads s.n s.rows s.low z).length hs hb7 hb5 hb4
  have hall := he.seq hreset
  have hcost' : t+(25*(selectedHeads s.n s.rows s.low z).length+22)+1≤
      61*F+22*(SignatureHeadLoader.localWork s z F+1)+58 := by omega
  refine ⟨rp,rm,rs,raw,shifted,_,hall,hcost',?_,
    result_reset_ready s z frame rp rm rs raw shifted hc hk hp hzr,hraw,hshift,?_⟩
  · exact reset_endpoint_bound b _ F hs hb2 hb4 hb5 hb8
      (result_raw_empty s z frame rp rm rs raw shifted) hbound hwidth
  · have hpref := StructuredSpace.local_stack_bound
      (compiled (.seq loadHead resetGeneratorCommand) 0 0)
      (a := frame.withPC (some (compiled (.seq loadHead resetGeneratorCommand) 0 0).entry))
      (steps := 61*F+22*(SignatureHeadLoader.localWork s z F+1)+58)
      (StreamResources.dataBits_le_mul _ hf)
    intro p q hp hq i
    exact (hpref p q (by omega) hq i).trans (by omega)


/-- The retained output cap itself is a fixed input polynomial, independent
of the caller's current storage bound and of the number of head reloads. -/
theorem retained_output_polynomial (s : Native.Inputs) (a : Data) (B : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a) :
    SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength B≤10000*(B+2)^6 := by
  let X := B+2
  have hX : 1≤X := by dsimp [X]; omega
  have hX2 : 1≤X^2 := one_le_pow₀ hX
  have h16 : X≤X^6 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤6)
  have h26 : X^2≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h56 : X^5≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h06 : 1≤X^6 := one_le_pow₀ hX
  have h13 : X≤X^3 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤3)
  have hi := NodeTime.inputBounds s a ha B hB
  have hc := (NodeTime.columns_le hi).2
  have hn : s.n≤X := hi.n.trans (by dsimp [X]; omega)
  have hN : s.N≤X := by
    have hb : s.N≤B := by simpa [ha.factors,unary] using hB 129
    dsimp [X]; omega
  have hD : s.D≤X := hi.D.trans (by dsimp [X]; omega)
  have hb : B≤X := by dsimp [X]; omega
  have hcol : s.columnLength≤102*X^3 := by
    apply hc.trans
    calc
      _≤X*(100*X^2+2) := by dsimp [X]; gcongr; omega
      _≤X*(102*X^2) := by gcongr; omega
      _=102*X^3 := by ring
  have hcB : s.columnLength+B≤103*X^3 := by omega
  calc
    _≤X*(2*X+2)+2+(2*X+2)*X+X*(12*X*(103*X^3)+6*X+1) := by
      unfold SignatureHeadLoader.retainedOutputBound
      gcongr
    _=1236*X^5+10*X^2+5*X+2 := by ring
    _≤10000*X^6 := by omega

/-- Both the time and every-prefix loader storage are bounded by one fixed
input polynomial. This envelope is transient and is never the next F. -/
def runEnvelope (B F : ℕ) : ℕ :=
  1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)*(F+B+2)^64

theorem load_run_polynomial (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (B : ℕ) (hB : WordBound B a) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame))
    (z F L : ℕ) (hz : frame.stacks headAddress=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval loadHead total frame (result s z frame rp rm rs raw shifted) ∧
      total≤runEnvelope B F ∧ WordBound F (result s z frame rp rm rs raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total →
        Trace (SignatureHeadLoader.programFrom headAddress) prefixSteps
          (frame.withPC (some (SignatureHeadLoader.programFrom headAddress).entry)) intermediate →
        dataBits intermediate≤runEnvelope B F := by
  obtain ⟨rp,rm,rs,raw,shifted,total,he,ht,hbound,hraw,hshift,hprefix⟩ :=
    load_run s a ha ra rd rc words hw frame hm z F L hz hf hW hout
  have hzF : z≤F := by simpa [hz,unary] using hf headAddress
  have hbudget := HeadLoaderBudgets.leafWork_le s a B F z ha hB hrows hzF
  let C := 10000000000000000*HeadLoaderBudgets.sizeCoefficient^8
  let X := (F+B+2)^64
  have hX : 1≤X := one_le_pow₀ (by omega)
  have hFX : F≤X := by
    apply (show F≤F+B+2 by omega).trans
    simpa only [pow_one] using pow_le_pow_right₀ (show 1≤F+B+2 by omega) (by decide : 1≤64)
  have hsmall : C*X≤runEnvelope B F := by
    change C*X≤1000*(C+3)*X
    exact Nat.mul_le_mul_right X (by omega)
  have hlocal : SignatureHeadLoader.localWork s z F≤C*X := by
    change 36*F+22*(SignatureHeadLoader.localWork s z F+1)+35≤C*X at hbudget
    omega
  refine ⟨rp,rm,rs,raw,shifted,total,he,(ht.trans hbudget).trans hsmall,
    hbound,hraw,hshift,?_⟩
  intro p q hp hq
  apply (hprefix p q hp hq).trans
  change 1000*(F+(SignatureHeadLoader.localWork s z F+1)+1)≤1000*(C+3)*X
  calc
    _≤1000*(X+C*X+2*X) := by omega
    _=1000*(C+3)*X := by
      have hfactor (x c : ℕ) : 1000*(x+c*x+2*x)=1000*(c+3)*x := by ring
      exact hfactor X C

section Storage
open SignatureTupleDFS SignatureTupleTraversal

/-- Reloading a head preserves the complete attained ancestor path. -/
theorem result_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth)
    (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth ancestors frame) :
    AncestorStorage h key levels base depth ancestors
      (result s z frame rp rm rs raw shifted) := by
  refine ⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 0) (by decide) (by decide)]
    exact ha.cursors
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 1) (by decide) (by decide)]
    exact ha.representatives
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 6) (by decide) (by decide)]
    exact ha.heads
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 9) (by decide) (by decide)]
    exact ha.address
  · rw [result_register_frame s z frame rp rm rs raw shifted controllerPorts.active (by decide)]
    exact ha.active

/-- A completed reload followed by the actual bounded counter initializer
establishes the next head's concrete scan boundary. -/
theorem result_reset_scan_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val)
    (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth.val ancestors frame)
    (hl : frame.regs controllerPorts.leaf=false)
    (hh : (selectedHeads s.n s.rows s.low z).length=h depth.val)
    (hc : frame.stacks (tupleStacks 2)=[]) (hk : frame.stacks (tupleStacks 3)=[])
    (hp : frame.stacks (tupleStacks 4)=[]) (ht : frame.stacks (tupleStacks 5)=[])
    (hz : frame.stacks (tupleStacks 8)=[]) :
    ScanStorage h key levels base depth ancestors 0
      (resetGeneratorState (result s z frame rp rm rs raw shifted)) := by
  apply reset_scan_storage h key levels base depth ancestors
  · exact result_ancestor_storage h key levels base depth.val ancestors s z frame rp rm rs raw shifted ha
  · rw [result_register_frame s z frame rp rm rs raw shifted controllerPorts.leaf (by decide)]
    exact hl
  · rw [result_headsize, hh]
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 2)
      (by decide) (by decide)).trans hc
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 3)
      (by decide) (by decide)).trans hk
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 4)
      (by decide) (by decide)).trans hp
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 5)
      (by decide) (by decide)).trans ht
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 8)
      (by decide) (by decide)).trans hz
  · exact result_raw_empty ..


/-- Internal descent retains only attained frames and the unary depth. Its
boundary bound depends on depth and word lengths, never on visited nodes. -/
theorem descend_endpoint_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth hmax F : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth<levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (hh : ∀ d<levels, h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)≤F)
    (hframe : ∀ i, (a.stacks i).length≤F) :
    ∀ i, ((descendClearState a).stacks i).length≤F := by
  have hb := descend_ancestor_storage h key levels base depth ancestors rep a hd ha hw hp
  have hf := hb.frame_bound h key hmax hh
  have hcleared := descendClearState_cleared a
  intro i
  by_cases hi : ∃ j : Fin 12, i=tupleStacks j
  · obtain ⟨j,rfl⟩ := hi
    fin_cases j
    · change ((descendClearState a).stacks (tupleStacks 0)).length≤F
      omega
    · change ((descendClearState a).stacks (tupleStacks 1)).length≤F
      omega
    · change ((descendClearState a).stacks (tupleStacks 2)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 3)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 4)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 5)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 6)).length≤F
      rw [hb.heads, List.length_replicate]
      omega
    · change ((descendClearState a).stacks (tupleStacks 7)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 8)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 9)).length≤F
      rw [hb.address, List.length_replicate]
      omega
    · change ((descendClearState a).stacks (tupleStacks 10)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 11)).length≤F
      rw [hcleared _ (by decide)]; simp
  · rw [descendClearState_outside_tuple a i (fun j hj => hi ⟨j,hj⟩)]
    exact hframe i


/-- After a parent reload, the bounded advance preserves the actual scanner
input and establishes the next assignment without replaying an old rescan. -/
theorem advance_candidate_ready (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ)
    (candidate next : Fin (2^h)) (hnext : next.val=candidate.val+1)
    (ready : CandidateReady a W rows h candidate) (hw : CursorWords a h candidate.val) :
    CandidateReady (advanceCandidateState a) W rows h next := by
  have hn := hw.advance candidate.isLt
  have hf (i : Fin 896) (hk : i≠tupleStacks 3) (hc : i≠candidatePorts.counter)
      (hr : i≠remainingPorts.counter) (hs : i≠remainingPorts.scratch) :
      (advanceCandidateState a).stacks i=a.stacks i :=
    advanceCandidateState_outside a hw.incrementScratch i hk hc hr hs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ready.offset
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ready.matrix
  · change (advanceCandidateState a).stacks candidatePorts.counter=_
    rw [hnext]
    exact hn.exact (by rw [←hnext]; exact next.isLt)
  · change Function.update (advanceState a).stacks (tupleStacks 3) [] (tupleStacks 3)=[]
    exact Function.update_self _ _ _
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ready.predecessor
  · intro i h0 h15 h16 h17 h18 h22
    have hsmall : ∀ j : Fin 24, j≠0 → j≠15 → j≠16 → j≠17 → j≠18 →
        (rescanStacks j).val<768 := by decide
    have hv := hsmall i h0 h15 h16 h17 h18
    have hne (j : Fin 896) (hj : 768≤j.val) : rescanStacks i≠j := by
      intro he
      have hh := congrArg Fin.val he
      omega
    rw [hf _ (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide))]
    exact ready.scratch i h0 h15 h16 h17 h18 h22

/-- Reloaded parent coefficients, restored cursor and an actual predecessor
copy give the next complete scanner input. -/
theorem resume_candidate_ready (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ)
    (candidate next : Fin (2^h)) (hnext : next.val=candidate.val+1)
    (hw : CursorWords a h candidate.val)
    (hW : a.stacks 141=W)
    (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words))
    (hh : a.stacks 651=List.replicate h false)
    (hk : a.stacks (tupleStacks 3)=[]) (hz : a.stacks (tupleStacks 8)=[])
    (hscratch : ∀ i : Fin 24, i≠0 → i≠15 → i≠16 → i≠17 → i≠18 → i≠22 →
      a.stacks (rescanStacks i)=[]) :
    CandidateReady (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)) W rows h next := by
  let b := SignatureTupleProgram.copyState 651 (tupleStacks 8) a
  have hf (i : Fin 896) (hi : i≠tupleStacks 8) : b.stacks i=a.stacks i := by
    simp only [b,SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne hi]
  have hzero : List.replicate h false=ExecCNFTupleEnumeration.fixedBits h 0 := by
    apply ExecCNFTupleEnumeration.word_eq_of_length_value
    · simp
    · simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))]
  have ready : CandidateReady b W rows h candidate := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [hf _ (by decide)]; exact hW
    · rw [hf _ (by decide)]; exact hrows
    · rw [hf _ (by decide)]; exact hw.exact candidate.isLt
    · rw [hf _ (by decide)]; exact hk
    · change Function.update a.stacks (tupleStacks 8)
        (a.stacks 651++a.stacks (tupleStacks 8)) (tupleStacks 8)=_
      rw [Function.update_self,hh,hz,List.append_nil]
      exact hzero
    · intro i h0 h15 h16 h17 h18 h22
      have hne : rescanStacks i≠tupleStacks 8 := fun he =>
        h18 (rescanStacks.injective he)
      rw [hf _ hne]
      exact hscratch i h0 h15 h16 h17 h18 h22
  exact advance_candidate_ready b W rows h candidate next hnext ready
    (copyPredecessor_cursor a h candidate.val hw)


theorem initialControlState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i≠tupleStacks j) :
    (initialControlState a).stacks i=a.stacks i := by
  change (SignatureTupleProgram.copyState 649 (tupleStacks 9) (SignatureTupleProgram.copyState 130 (tupleStacks 6)
    (initialClearState a))).stacks i=_
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (hi 9),
    Function.update_of_ne (hi 6)]
  rw [initialClearState,clearWordsState_stacks,ite_eq_right]
  intro hm
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
  exact hi j hj.symm

/-- Initializing controller words restores the input cap before the first
matrix loader is invoked. -/
theorem initialControl_endpoint_bound (a : State 40 896) (levels base F : ℕ)
    (hh : a.stacks 130=List.replicate levels true)
    (hz : a.stacks 649=List.replicate base true)
    (hframe : ∀ i, (a.stacks i).length≤F) :
    ∀ i, ((initialControlState a).stacks i).length≤F := by
  have hwords := initializeLevelsState_words (initialClearState a) levels base
    ((initialClearState_source130 a).trans hh) ((initialClearState_source649 a).trans hz)
    (initialClearState_tuple a 6) (initialClearState_tuple a 9)
  have hl := hframe 130
  have hb := hframe 649
  rw [hh,List.length_replicate] at hl
  rw [hz,List.length_replicate] at hb
  intro i
  by_cases hi : ∃ j : Fin 12, i=tupleStacks j
  · obtain ⟨j,rfl⟩ := hi
    by_cases h6 : j=6
    · subst j
      change ((initializeLevelsState (initialClearState a)).stacks (tupleStacks 6)).length≤F
      rw [hwords.1,List.length_replicate]
      exact hl
    by_cases h9 : j=9
    · subst j
      change ((initializeLevelsState (initialClearState a)).stacks (tupleStacks 9)).length≤F
      rw [hwords.2,List.length_replicate]
      exact hb
    rw [initialControlState_tuple a j h6 h9,List.length_nil]
    exact Nat.zero_le _
  · rw [initialControlState_outside_tuple a i (fun j hj => hi ⟨j,hj⟩)]
    exact hframe i


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

private theorem master_not_latch (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i≠rescanStacks 22 := by
  intro he
  have hv := congrArg Fin.val he
  have heq : i=(362 : Fin 768) := Fin.ext hv
  subst i
  exact (by decide : (362 : Fin 768)∉SignatureHeadLoader.masters) hi

/-- The actual probe and attained descent preserve every loader source word
and native cache; only bounded cursor frames and the scanner latch change. -/
theorem fresh_descent_masters (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2^h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch=[])
    (base : Data) (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (descendClearState (probePostState a out W rows h candidate))) := by
  constructor
  intro i hi
  exact (fresh_descent_stack_frame a out W rows h candidate ready hs
    (SignatureHeadLoader.lowStacks i) (low_outside_tuple i) (master_not_latch i hi)).trans
    (hm.stored i hi)

theorem initialControl_masters (a : State 40 896) (base : Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (initialControlState a)) := by
  constructor
  intro i hi
  exact (initialControlState_outside_tuple a (SignatureHeadLoader.lowStacks i)
    (low_outside_tuple i)).trans (hm.stored i hi)

theorem parent_return_masters (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth+1)) (a : State 40 896) (base : Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (parentReturnState h key depth ancestors a)) := by
  constructor
  intro i hi
  exact (parentReturnState_outside_tuple h key depth ancestors a
    (SignatureHeadLoader.lowStacks i) (low_outside_tuple i)).trans (hm.stored i hi)

/-- Reloading changes the current matrix, while the restored bounded
candidate and remaining-assignment words retain their exact values. -/
theorem result_cursor_words (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (h c : ℕ) (hw : CursorWords frame h c) :
    CursorWords (result s z frame rp rm rs raw shifted) h c := by
  have hc := result_high_frame s z frame rp rm rs raw shifted
    candidatePorts.counter (by decide) (by decide)
  have hr := result_high_frame s z frame rp rm rs raw shifted
    remainingPorts.counter (by decide) (by decide)
  have hs := result_high_frame s z frame rp rm rs raw shifted
    remainingPorts.scratch (by decide) (by decide)
  refine ⟨hw.range,?_,?_,?_,?_,?_,?_⟩
  · rw [hc]; exact hw.value
  · rw [hc]; exact hw.width
  · intro hn; rw [hc]; exact hw.exact hn
  · rw [hr]; exact hw.remaining
  · exact result_raw_empty ..
  · rw [hs]; exact hw.decrementScratch


/-- The first positive-depth scan is reached by the actual fixed setup,
actual native head loader, and actual bounded counter initializer. -/
theorem setup_native_run (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (base F L : ℕ) (hbase : a.stacks 649=unary base) (hpositive : 0<s.r)
    (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval (setupWith loadHead) total a
        (resetGeneratorState (result s base (initialControlState a) rp rm rs raw shifted)) ∧
      total+1≤runEnvelope B F+63*F+73 ∧
      WordBound F (resetGeneratorState
        (result s base (initialControlState a) rp rm rs raw shifted)) ∧
      CandidateReady (resetGeneratorState
        (result s base (initialControlState a) rp rm rs raw shifted))
        (a.stacks 141) shifted (selectedHeads s.n s.rows s.low base).length
        ⟨0,Nat.pow_pos (by decide)⟩ ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low base) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (setupWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  have hheads : a.stacks 130=unary s.r :=
    (hm.stored 130 (by decide)).trans
      ((Native.start_low s source ra rd rc words 130 (by decide)).trans ha.colors)
  let b := initialControlState a
  have hb : WordBound F b := initialControl_endpoint_bound a s.r base F hheads hbase hf
  have hbm := initialControl_masters a _ hm
  have haddr : b.stacks headAddress=unary base := by
    exact (initializeLevelsState_words (initialClearState a) s.r base
      ((initialClearState_source130 a).trans hheads) ((initialClearState_source649 a).trans hbase)
      (initialClearState_tuple a 6) (initialClearState_tuple a 9)).2
  have hbW : b.stacks 141=a.stacks 141 :=
    initialControlState_outside_tuple a 141 (low_outside_tuple 141)
  have hblank (i : Fin 12) (h6 : i≠6) (h9 : i≠9) : b.stacks (tupleStacks i)=[] :=
    initialControlState_tuple a i h6 h9
  obtain ⟨rp,rm,rs,raw,shifted,loadSteps,hload,hloadTime,hloaded,hraw,hshift,_⟩ :=
    load_run_polynomial s source ha B hB hrows ra rd rc words hw b hbm base F L haddr hb
      (by simpa only [hbW] using hW) hout
  let loaded := result s base b rp rm rs raw shifted
  have hhigh (i : Fin 12) (hi : i≠10) (hj : i≠11) : loaded.stacks (tupleStacks i)=b.stacks (tupleStacks i) := by
    apply result_high_frame
    · change 768≤836+i.val; omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      constructor
      · intro he
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val he
        change 836+i.val=846 at hv
        omega
      · intro he
        apply hj
        apply Fin.ext
        have hv := congrArg Fin.val he
        change 836+i.val=847 at hv
        omega
  have hh := result_headsize s base b rp rm rs raw shifted
  have hwidth : (selectedHeads s.n s.rows s.low base).length+1≤F :=
    (Nat.add_le_add_right (Bounds.selectedHeads_length s.n s.rows s.low base) 1).trans
      ((retainedOutputBound_headroom s.n s.N s.D s.columnLength L).trans hout)
  obtain ⟨total,he,hend,hprefix,ht⟩ := setup_loaded_run_space loadHead a loaded
    s.r base (selectedHeads s.n s.rows s.low base).length F loadSteps hpositive hheads hbase hload hh
    ((hhigh 2 (by decide) (by decide)).trans (hblank 2 (by decide) (by decide)))
    ((hhigh 4 (by decide) (by decide)).trans (hblank 4 (by decide) (by decide)))
    ((hhigh 5 (by decide) (by decide)).trans (hblank 5 (by decide) (by decide)))
    ((hhigh 7 (by decide) (by decide)).trans (hblank 7 (by decide) (by decide)))
    ((hhigh 8 (by decide) (by decide)).trans (hblank 8 (by decide) (by decide)))
    (result_raw_empty s base b rp rm rs raw shifted) hf hloaded hwidth
  have ready := result_reset_ready s base b rp rm rs raw shifted
    (hblank 2 (by decide) (by decide)) (hblank 3 (by decide) (by decide))
    (hblank 4 (by decide) (by decide)) (hblank 8 (by decide) (by decide))
  rw [hbW] at ready hshift
  refine ⟨rp,rm,rs,raw,shifted,total,he,by omega,hend,ready,hraw,hshift,?_⟩
  intro p q hp hq i
  exact (hprefix p q hp hq i).trans (by omega)


/-- Returning to a parent uses the actual native reload and advances its
restored cursor once. No earlier predecessor scan is repeated. -/
theorem ascend_native_run (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) (depth.val+1))
    (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hanc : AncestorStorage h key levels base (depth.val+1) ancestors a)
    (F L hmax : ℕ) (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hh : ∀ d<levels,h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)+(hmax+1)≤F)
    (hsize : (selectedHeads s.n s.rows s.low (base+depth.val)).length=h depth.val) :
    ∃ rp rm rs raw shifted total,
      let loaded := result s (base+depth.val) (parentReturnState h key depth.val ancestors a)
        rp rm rs raw shifted
      let finish := advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) loaded)
      Eval (ascendWith loadHead) total a finish ∧
      total+1≤runEnvelope B F+69*F+100 ∧ WordBound F finish ∧
      ScanStorage h key levels base depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) finish ∧
      (∀ hn : (ancestors (Fin.last depth.val)).val.val+1<2^h depth.val,
        CandidateReady finish (a.stacks 141) shifted (h depth.val) ⟨_,hn⟩) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low (base+depth.val)) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (ascendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  let b := parentReturnState h key depth.val ancestors a
  have hb := parent_return_endpoint_bound h key levels base depth.val hmax F ancestors a hanc hh hcap hf
  have hbm := parent_return_masters h key depth.val ancestors a _ hm
  have hbanc := parent_return_ancestor_storage h key levels base depth.val ancestors a hanc
  have hbw := parent_return_cursor h key depth.val ancestors a
  have hbW : b.stacks 141=a.stacks 141 :=
    parentReturnState_outside_tuple h key depth.val ancestors a 141 (low_outside_tuple 141)
  have hblank (i : Fin 896) (hi : i∈currentHeadPorts)
      (h2 : i≠tupleStacks 2) (h7 : i≠tupleStacks 7) : b.stacks i=[] :=
    parent_return_current_empty h key depth.val ancestors a i hi h2 h7
  obtain ⟨rp,rm,rs,raw,shifted,loadSteps,hload,hloadTime,hloaded,hraw,hshift,_⟩ :=
    load_run_polynomial s source ha B hB hrows ra rd rc words hw b hbm (base+depth.val) F L
      hbanc.address hb (by simpa only [hbW] using hW) hout
  let loaded := result s (base+depth.val) b rp rm rs raw shifted
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      loaded.stacks i=b.stacks i := result_high_frame s (base+depth.val) b rp rm rs raw shifted i hi hne
  have hloadedWords := result_cursor_words s (base+depth.val) b rp rm rs raw shifted _ _ hbw
  have hwidth : loaded.stacks 651=List.replicate (h depth.val) false := by
    rw [result_headsize,hsize]
  have hpred : loaded.stacks (tupleStacks 8)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hpayload : loaded.stacks (tupleStacks 4)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hsaved : loaded.stacks (tupleStacks 3)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hcursor : h depth.val+1≤F := by have := hh depth.val depth.isLt; omega
  obtain ⟨total,he,hend,hprefix,ht⟩ := ascend_loaded_run_space h key loadHead depth.val F loadSteps
    ancestors a loaded hanc.cursors hanc.representatives hload hloadedWords hwidth hpred hf hloaded hcursor
  have hl : loaded.regs controllerPorts.leaf=false := by
    rw [result_register_frame s (base+depth.val) b rp rm rs raw shifted controllerPorts.leaf (by decide)]
    rfl
  have hscan := resume_loaded_storage h key levels base depth (Fin.init ancestors)
    (ancestors (Fin.last depth.val)).val.val loaded
    (result_ancestor_storage h key levels base depth.val (Fin.init ancestors)
      s (base+depth.val) b rp rm rs raw shifted hbanc)
    hloadedWords (ancestors (Fin.last depth.val)).val.isLt hl hwidth hpayload hpred
  rw [hbW] at hshift
  refine ⟨rp,rm,rs,raw,shifted,total,he,by omega,hend,hscan,?_,hraw,hshift,?_⟩
  · intro hn
    apply resume_candidate_ready loaded (a.stacks 141) shifted (h depth.val)
      (ancestors (Fin.last depth.val)).val ⟨_,hn⟩ rfl hloadedWords
    · exact (result_offset s (base+depth.val) b rp rm rs raw shifted).trans hbW
    · exact result_matrix ..
    · exact hwidth
    · exact hsaved
    · exact hpred
    · exact result_rescan_scratch s (base+depth.val) b rp rm rs raw shifted
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by omega)


/-- An attained internal child is reached by actual frame pushes, cleanup,
head loading and bounded counter setup, with the same retained cap F. -/
theorem descend_native_run (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (hd : depth+1<levels)
    (s : Native.Inputs) (source : Data) (ha : Native.Ready s source)
    (B : ℕ) (hB : WordBound B source) (hrows : s.rows.length=s.n+s.N)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hcaches : CacheCorrect s.height (unary s.R) s.width words)
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hanc : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (F L hmax : ℕ) (hf : WordBound F a) (hW : (a.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F)
    (hh : ∀ d<levels,h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)+(hmax+1)≤F)
    (hsize : (selectedHeads s.n s.rows s.low (base+(depth+1))).length=h (depth+1)) :
    ∃ rp rm rs raw shifted total,
      let loaded := result s (base+(depth+1)) (descendClearState a) rp rm rs raw shifted
      let finish := resetGeneratorState loaded
      Eval (descendWith loadHead) total a finish ∧
      total+1≤runEnvelope B F+100*F+100 ∧ WordBound F finish ∧
      ScanStorage h key levels base ⟨depth+1,hd⟩ (Fin.snoc ancestors rep) 0 finish ∧
      CandidateReady finish (a.stacks 141) shifted (h (depth+1)) ⟨0,Nat.pow_pos (by decide)⟩ ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low (base+(depth+1))) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total+1 →
        Trace (compiled (descendWith loadHead) 0 0) prefixSteps
          (a.withPC (some (compiled (descendWith loadHead) 0 0).entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤2000*(F+1)+runEnvelope B F := by
  let b := descendClearState a
  have hbanc := descend_ancestor_storage h key levels base depth ancestors rep a (by omega) hanc hw hp
  have hb := descend_endpoint_bound h key levels base depth hmax F ancestors rep a (by omega)
    hanc hw hp hh (by omega) hf
  have hbm : SignatureHeadLoader.MasterFrame (Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
    constructor
    intro i hi
    exact (descendClearState_outside_tuple a (SignatureHeadLoader.lowStacks i)
      (low_outside_tuple i)).trans (hm.stored i hi)
  have hbW : b.stacks 141=a.stacks 141 :=
    descendClearState_outside_tuple a 141 (low_outside_tuple 141)
  have hblank := descendClearState_cleared a
  obtain ⟨rp,rm,rs,raw,shifted,loadSteps,hload,hloadTime,hloaded,hraw,hshift,_⟩ :=
    load_run_polynomial s source ha B hB hrows ra rd rc words hcaches b hbm (base+(depth+1)) F L
      hbanc.address hb (by simpa only [hbW] using hW) hout
  let loaded := result s (base+(depth+1)) b rp rm rs raw shifted
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      loaded.stacks i=b.stacks i := result_high_frame s (base+(depth+1)) b rp rm rs raw shifted i hi hne
  have hwidth : loaded.stacks 651=List.replicate (h (depth+1)) false := by rw [result_headsize,hsize]
  have hremaining : loaded.stacks (tupleStacks 7)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))
  have hscratch : loaded.stacks (tupleStacks 5)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))
  have hpayload : loaded.stacks (tupleStacks 4)=[] :=
    (hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))
  have hl : b.regs controllerPorts.leaf=false := descend_internal_leaf_flag a
    (levels-(depth+1)) (base+depth) (by omega)
    (by rw [hanc.heads]; congr 1; omega) hanc.address
  have he := descend_internal_eval loadHead a loaded (h depth) rep.val.val (h (depth+1)) loadSteps
    (hw.exact rep.val.isLt) hw.remaining hp hw.decrementScratch hl hload hwidth
    hremaining hscratch hpayload
  have hscan := result_reset_scan_storage h key levels base ⟨depth+1,hd⟩ (Fin.snoc ancestors rep)
    s (base+(depth+1)) b rp rm rs raw shifted hbanc hl hsize
    (hblank _ (by decide)) (hblank _ (by decide)) (hblank _ (by decide))
    (hblank _ (by decide)) (hblank _ (by decide))
  have hready := result_reset_ready s (base+(depth+1)) b rp rm rs raw shifted
    (hblank _ (by decide)) (hblank _ (by decide)) (hblank _ (by decide)) (hblank _ (by decide))
  rw [hbW,hsize] at hready
  rw [hbW] at hshift
  have hchild : h (depth+1)+1≤F := by have := hh (depth+1) hd; omega
  have hend := reset_endpoint_bound loaded (h (depth+1)) F hwidth
    ((hhigh _ (by decide) (by decide)).trans (hblank _ (by decide))) hpayload hscratch
    ((hhigh _ (by decide) (by decide)).trans (hblank _ (by decide)))
    (result_raw_empty s (base+(depth+1)) b rp rm rs raw shifted) hloaded hchild
  have hclear := clearWordsTime_le_on currentHeadPorts _ F (descend_current_bound a F hp hf)
  change clearWordsTime currentHeadPorts _≤8*(2*F+3) at hclear
  have hcurrent := hh depth (by omega)
  have htime : 22*h depth+25*h (depth+1)+loadSteps+
      clearWordsTime currentHeadPorts (descendLevelState (SignatureTupleRefinement.retainedState a))+53+1≤
      runEnvelope B F+100*F+100 := by omega
  refine ⟨rp,rm,rs,raw,shifted,_,he,htime,hend,hscan,hready,hraw,hshift,?_⟩
  have hpref := StructuredSpace.local_stack_bound (compiled (descendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (descendWith loadHead) 0 0).entry))
    (steps := runEnvelope B F+100*F+100) (StreamResources.dataBits_le_mul _ hf)
  intro p q hpn hq i
  exact (hpref p q (by omega) hq i).trans (by omega)


/-- The native loader leaves its requested physical address on low649.
This is needed when a later pair restarts the same tuple traversal. -/
theorem result_address649 (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 649=frame.stacks headAddress := by
  change (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks 649)=_
  rw [result_low s z frame rp rm rs raw shifted 649 (by decide) (by decide) (by decide)]
  rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ 649
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact SignatureHeadLoader.addressStateFrom_value headAddress _ (by decide)

theorem reset_result_address649 (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (resetGeneratorState (result s z frame rp rm rs raw shifted)).stacks 649=frame.stacks headAddress := by
  rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
  exact result_address649 ..


/-- Root exhaustion preserves the last root address, so the next pair can
initialize its traversal from low649 again. -/
theorem exhausted_root_address649 (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch=[]) :
    (rootAscendState (testAvailableState a)).stacks 649=a.stacks 649 := by
  rw [checkedReturnState_stack,ite_eq_right (by decide),testAvailableState_stacks a hs]

/-- The source compiler's conditional and sequence rules compose one
actual fresh probe and actual descent on a single bounded-prefix run. -/
theorem fresh_body_prefix_bound (load visit : Cmd 40 896)
    (a b c : State 40 896) (np nd D : ℕ)
    (hl : a.regs controllerPorts.leaf=false)
    (ha : b.regs controllerPorts.available=true) (hf : b.regs controllerPorts.fresh=true)
    (hp : Eval (probeWith candidateCall) np a b)
    (hd : Eval (descendWith load) nd b c)
    (hps : ∀ p q, p≤np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i,(q.stacks i).length≤D)
    (hds : ∀ p q, p≤nd → Trace (compiled (descendWith load) 0 0) p
      (b.withPC (some (compiled (descendWith load) 0 0).entry)) q →
      ∀ i,(q.stacks i).length≤D) :
    ∀ p q, p≤np+nd+4 →
      Trace (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines load candidateCall visit)) 0 0).entry)) q →
      ∀ i,(q.stacks i).length≤D := by
  let freshBranch : Cmd 40 896 := .ite controllerPorts.fresh (descendWith load) advanceCandidateCommand
  let availableBranch : Cmd 40 896 := .ite controllerPorts.available freshBranch (ascendWith load)
  have hfe : Eval freshBranch (nd+1) b c := .ite_true hf hd
  have hfs := StructuredSpace.conditional_true_stack_bound
    (no := advanceCandidateCommand) hf hd 0 0 hds
    (compiled freshBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have haveval : Eval availableBranch (nd+1+1) b c := .ite_true ha hfe
  have havspace := StructuredSpace.conditional_true_stack_bound
    (no := ascendWith load) ha hfe 0 0 hfs
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq haveval
  have hsseq := StructuredSpace.sequence_stack_bound hp haveval 0 0 hps havspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (np+(nd+1+1)+1) a c := .ite_false hl hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith load)) hl hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hhalt := StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole
  intro p q hpq hq i
  exact hhalt p q (by omega) hq i


/-- Restoring the predecessor and advancing a resumed cursor leave the
freshly loaded parent address on low649. -/
theorem resume_loaded_address649 (a : State 40 896) (h c : ℕ)
    (hw : CursorWords a h c) :
    (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)).stacks 649=a.stacks 649 := by
  have hc := copyPredecessor_cursor a h c hw
  rw [advanceCandidateState_outside _ hc.incrementScratch 649
    (by decide) (by decide) (by decide) (by decide)]
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (by decide : (649:Fin 896)≠tupleStacks 8)]


/-- One fixed input polynomial bounds both the candidate scanner's retained
key and its transient space. The numerical candidate value is absent. -/
def scannerEnvelope (B : ℕ) : ℕ := 100000*(20000*(B+2)^6)^6

theorem scanner_caps_polynomial (s : Native.Inputs) (source : Data) (B z : ℕ)
    (ha : Native.Ready s source) (hB : WordBound B source) (W : List Bool) (hW : W.length≤B)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    let h := (selectedHeads s.n s.rows s.low z).length
    let C := 3*(s.columnLength+B)+1
    AttainedSignatureProgram.Rescan.polynomialBudget W shifted h C ≤ scannerEnvelope B ∧
      AttainedSignatureProgram.Rescan.spaceBudget W shifted h C ≤ scannerEnvelope B ∧
      AttainedSignatureProgram.Rescan.keyBound W h shifted.length C ≤ scannerEnvelope B := by
  dsimp only
  let X := B+2
  let C := 3*(s.columnLength+B)+1
  let R := SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength B
  let S := 1+B+s.D+s.n+C+R
  have hX : 1≤X := by dsimp [X]; omega
  have hX2 : 1≤X^2 := one_le_pow₀ hX
  have h16 : X≤X^6 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤6)
  have h36 : X^3≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h06 : 1≤X^6 := one_le_pow₀ hX
  have hi := NodeTime.inputBounds s source ha B hB
  have hcol := (NodeTime.columns_le hi).2
  have hcol' : s.columnLength≤102*X^3 := by
    apply hcol.trans
    calc
      _≤X*(100*X^2+2) := by dsimp [X]; gcongr; omega
      _≤X*(102*X^2) := by gcongr; omega
      _=102*X^3 := by ring
  have hb : B≤X^6 := (show B≤X by dsimp [X]; omega).trans h16
  have hrCap : R≤10000*X^6 := retained_output_polynomial s source B ha hB
  have hnB := hi.n
  have hDB := hi.D
  have hS : S≤20000*X^6 := by dsimp [S,C]; omega
  have hpositive : 1≤S := by dsimp [S]; omega
  have hn : (selectedHeads s.n s.rows s.low z).length ≤ s.n := Bounds.selectedHeads_length ..
  have hlen : shifted.length=s.D := hy.length_eq.symm.trans
    (LayoutMatrixProgram.matrixRel_dimensions hr).1
  have hmatrix := SignatureHeadLoader.shifted_matrix_word_length W hr hy
  have hmatrix' : (Subexp.MatrixProgramSupport.words
      (shifted.map Subexp.MatrixProgramSupport.words)).length≤R := by
    apply hmatrix.trans
    apply le_trans (Nat.mul_le_mul_left s.D (show
      12*(selectedHeads s.n s.rows s.low z).length*(s.columnLength+W.length)+
        6*(selectedHeads s.n s.rows s.low z).length+1≤
      12*s.n*(s.columnLength+B)+6*s.n+1 by gcongr))
    dsimp [R,SignatureHeadLoader.retainedOutputBound]
    omega
  have hs := AttainedSignatureProgram.Rescan.budgets_le_monomial W shifted
    (selectedHeads s.n s.rows s.low z).length C S hpositive
    (by dsimp [S]; omega) (by rw [hlen]; dsimp [S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hbudget : 100000*S^6 ≤ scannerEnvelope B :=
    Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hS 6)
  have hp := hs.1.trans hbudget
  have hkey : AttainedSignatureProgram.Rescan.keyBound W
      (selectedHeads s.n s.rows s.low z).length shifted.length C≤
      AttainedSignatureProgram.Rescan.polynomialBudget W shifted
        (selectedHeads s.n s.rows s.low z).length C := by
    unfold AttainedSignatureProgram.Rescan.polynomialBudget
    omega
  exact ⟨hp,hs.2.trans hbudget,hkey.trans hp⟩

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
