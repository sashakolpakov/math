import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSupport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
/-- The physical result of that one concrete head loader. -/
def result (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    State 40 896 :=
  SignatureHeadLoader.leafOutputFrom 843 frame
    (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom 843 frame)
      rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted)

theorem result_high_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
    (result s z frame rp rm rs raw shifted).stacks i=frame.stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id i).trans
    (SignatureHeadLoader.lowResultFrom_frame 843 _ _ i hi hne)

theorem result_register_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (result s z frame rp rm rs raw shifted).regs i=frame.regs i :=
  SignatureHeadLoader.leafOutputFrom_registers 843 frame _ i hi

theorem result_low (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom 843 frame)
        rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id (SignatureHeadLoader.lowStacks i)).trans
    (SignatureHeadLoader.lowResultFrom_low 843 _ _ i h659 h668 h669)

theorem result_offset (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 141=frame.stacks 141 := by
  rw [show (141 : Fin 896)=SignatureHeadLoader.lowStacks 141 from rfl,
    result_low s z frame rp rm rs raw shifted 141 (by decide) (by decide) (by decide)]
  rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ 141
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact SignatureHeadLoader.addressStateFrom_frame 843 _ 141 (by decide)

theorem result_headsize (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 651=
      List.replicate (selectedHeads s.n s.rows s.low z).length false := by
  exact (SignatureHeadLoader.leafFrom_head_outputs 843 frame _ _ rp rm rs
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
  SignatureHeadLoader.leafOutputFrom_raw_empty 843 frame _

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
  exact (SignatureHeadLoader.leafInputFrom_masters 843 frame base hf).trans
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
  have hin := SignatureHeadLoader.leafInputFrom_wordBound 843 frame F (by decide) hf
  have hw : (SignatureHeadLoader.leafInputFrom 843 frame).stacks 141=frame.stacks 141 :=
    SignatureHeadLoader.addressStateFrom_frame 843 _ 141 (by decide)
  have hb := SignatureHeadLoader.localResult_retained_bound
    (SignatureHeadLoader.leafInputFrom 843 frame) rp rm rs s.n s.N (s.Q*s.r) z F s.D
    s.columnLength L s.rows s.low raw shifted s.relation hin (by simpa only [hw] using hW)
    hr (by simpa only [hw] using hy)
  rw [Nat.max_eq_left hout] at hb
  exact SignatureHeadLoader.leafOutputFrom_wordBound 843 frame _ F F
    (by decide) le_rfl hf hb

/-- The complete loader run is obtained from actual native inputs and paid
cache values. No successful matrix execution is an input to this theorem. -/
theorem load_run (s : Native.Inputs) (a : Data) (ha : Native.Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (frame : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame))
    (z F L : ℕ) (hz : frame.stacks 843=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval (.call (SignatureHeadLoader.programFrom 843)) total frame (result s z frame rp rm rs raw shifted) ∧
      total≤36*F+22*(SignatureHeadLoader.localWork s z F+1)+35 ∧
      WordBound F (result s z frame rp rm rs raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total →
        Trace (SignatureHeadLoader.programFrom 843) prefixSteps
          (frame.withPC (some (SignatureHeadLoader.programFrom 843).entry)) intermediate →
        dataBits intermediate≤1000*(F+(SignatureHeadLoader.localWork s z F+1)+1) := by
  obtain ⟨rp,rm,rs,raw,shifted,total,ht,htr,hr,hy,hprefix⟩ :=
    SignatureHeadLoader.native_leafFrom_run_space 843 s a ha ra rd rc words hw frame hm
      z F (by decide) hz hf
  exact ⟨rp,rm,rs,raw,shifted,total,.call _ htr,ht,
    result_wordBound s z F L frame rp rm rs raw shifted hf hW hout hr hy,hr,hy,hprefix⟩

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
    (z F L : ℕ) (hz : frame.stacks 843=unary z) (hf : WordBound F frame)
    (hW : (frame.stacks 141).length≤L)
    (hout : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L≤F) :
    ∃ rp rm rs raw shifted total,
      Eval (.call (SignatureHeadLoader.programFrom 843)) total frame (result s z frame rp rm rs raw shifted) ∧
      total≤runEnvelope B F ∧ WordBound F (result s z frame rp rm rs raw shifted) ∧
      LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
        (selectedHeads s.n s.rows s.low z) raw ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (frame.stacks 141))) raw shifted ∧
      ∀ prefixSteps intermediate, prefixSteps≤total →
        Trace (SignatureHeadLoader.programFrom 843) prefixSteps
          (frame.withPC (some (SignatureHeadLoader.programFrom 843).entry)) intermediate →
        dataBits intermediate≤runEnvelope B F := by
  obtain ⟨rp,rm,rs,raw,shifted,total,he,ht,hbound,hraw,hshift,hprefix⟩ :=
    load_run s a ha ra rd rc words hw frame hm z F L hz hf hW hout
  have hzF : z≤F := by simpa [hz,unary] using hf 843
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

section Outputs
variable (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))

theorem result_head_outputs :
    let e := result s z frame rp rm rs raw shifted
    let js := selectedHeads s.n s.rows s.low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask s.n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate s.rows s.n z) s.N).map
        Encoding.encodeNat) :=
  SignatureHeadLoader.leafFrom_head_outputs 843 frame _ _ rp rm rs
    s.n s.N (s.Q*s.r) z s.rows s.low raw shifted

theorem result_mask_word :
    (result s z frame rp rm rs raw shifted).stacks 670 =
      List.ofFn (fun v : Fin s.n => HeadIdentifierProgram.predicate s.rows s.low z v.val) := by
  rw [(result_head_outputs s z frame rp rm rs raw shifted).2.2.1]
  exact HeadIdentifierProgram.support_mask_eq _ _

theorem result_mask_length :
    ((result s z frame rp rm rs raw shifted).stacks 670).length=s.n := by
  rw [result_mask_word,List.length_ofFn]

theorem result_mask_count :
    HighIncidenceProgram.Restriction.highCount ((result s z frame rp rm rs raw shifted).stacks 670)=
      (selectedHeads s.n s.rows s.low z).length := by
  rw [result_mask_word]
  exact HeadRepresentativeSemantics.headOrder_highCount _ _

theorem result_protected_frame (i : Fin 768) (hp : Protected i)
    (hne : i∉([649,650,651,652,659,668,669,670,671] : List (Fin 768))) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      frame.stacks (SignatureHeadLoader.lowStacks i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  rcases hne with ⟨h649,h650,h651,h652,h659,h668,h669,h670,h671⟩
  rw [result_low s z frame rp rm rs raw shifted i h659 h668 h669,
    SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ i hp
      h650 h651 h652 h668 h669 h670 h671]
  apply SignatureHeadLoader.addressStateFrom_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have hv := congrArg (fun j : Fin 896 => j.val) h
    exact h649 (Fin.ext hv)
  · intro h
    have hv := congrArg (fun j : Fin 896 => j.val) h
    exact h659 (Fin.ext hv)
  · intro h
    have hv := congrArg Fin.val h
    change i.val=846 at hv
    have := i.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val=847 at hv
    have := i.isLt
    omega

theorem result_query_master_frame :
    QueryTupleState.QueryMasterFrame frame (result s z frame rp rm rs raw shifted) := by
  constructor
  intro i hi
  simp only [QueryTupleState.masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact result_protected_frame s z frame rp rm rs raw shifted 78 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 128 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 129 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 130 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 131 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 132 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 133 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 134 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 135 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 136 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 138 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 139 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 140 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 141 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 194 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 201 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 202 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 203 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 204 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 207 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 209 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 211 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 212 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 243 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 256 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 280 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 281 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 300 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 301 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 302 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 305 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 307 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 320 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 322 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 338 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 640 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 641 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 642 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 647 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 700 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 701 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 702 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 703 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 704 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 705 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 706 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 707 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 708 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 709 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 710 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 711 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 712 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 713 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 714 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 715 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 716 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 717 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 718 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 719 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 728 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 730 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 731 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 732 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 733 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 734 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 735 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 736 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 737 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 738 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 739 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 740 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 741 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 742 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 743 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 832 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 833 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 834 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 835 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 850 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 857 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 858 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 863 (by decide) (by decide)

end Outputs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
