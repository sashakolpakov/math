import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramModel
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSpecializationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram

open OAI BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The correction test is an actual fixed bit program; the whole prefix
storage bound is polynomial in the ambient assignment and scalar word sizes. -/
theorem correction_scan {n W : ℕ} {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (decode : List Bool → R) (zero one : List Bool)
    (hzero : decode zero = 0) (hone : decode one = 1)
    (hz : zero.length = W) (ho : one.length = W) (r : Fin 8 → Bool)
    (a : Fin n → Bool) (E : Finset (Fin n)) (head : Fin n → G) (g : G) :
    ∃ rf out,
      Trace LeafWeightProgram.Native.program (29 * n + 7 * W + 26)
        ((LeafWeightProgram.Native.data r (List.ofFn a)
          (LeafWeightProgram.supportBits ⟨E⟩) (LeafWeightProgram.headBits head g)
          zero one [] [] [] []).withPC (some LeafWeightProgram.Native.program.entry))
        ((LeafWeightProgram.Native.data rf (List.ofFn a)
          (LeafWeightProgram.supportBits ⟨E⟩) (LeafWeightProgram.headBits head g)
          zero one [] [] [] out).withPC none) ∧
      decode out = (if ∀ v ∈ E, head v = g → a v = true then 1 else 0) ∧
      out.length = W ∧
      ∀ j ≤ 29 * n + 7 * W + 26, ∀ c,
        Trace LeafWeightProgram.Native.program j
          ((LeafWeightProgram.Native.data r (List.ofFn a)
            (LeafWeightProgram.supportBits ⟨E⟩) (LeafWeightProgram.headBits head g)
            zero one [] [] [] []).withPC (some LeafWeightProgram.Native.program.entry)) c →
        dataBits c ≤ 32 * n + 9 * W + 26 := by
  obtain ⟨rf, out, ht, hd, hl⟩ :=
    LeafWeightProgram.program_localBoolWeight decode zero one W hzero hone hz ho
      r a ⟨E⟩ head g
  refine ⟨rf, out, ht, ?_, hl, ?_⟩
  · rw [hd, ← LeafWeightProgram.localBoolWeight_eq]
    congr 1
    exact propext (LeafWeightProgram.selected_iff a ⟨E⟩ head g)
  · intro j hj c hc
    have hb := trace_dataBits LeafWeightProgram.Native.program hc
    have hi : dataBits
        ((LeafWeightProgram.Native.data r (List.ofFn a)
          (LeafWeightProgram.supportBits ⟨E⟩) (LeafWeightProgram.headBits head g)
          zero one [] [] [] []).withPC
            (some LeafWeightProgram.Native.program.entry)) = 3 * n + 2 * W := by
      simp [dataBits, stackBits,
        LeafWeightProgram.Native.tapes,
        LeafWeightProgram.supportBits, LeafWeightProgram.headBits,
        Fin.sum_univ_succ, hz, ho]
      omega
    rw [hi] at hb
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.CorrectionGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafWeightProgram.Native

def command : Cmd 8 10 := .seq (copy 0 5)
  (.seq (copy 1 6) (.seq (copy 2 7) scan))

private theorem copy_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 10) ≠ dst)
    (r : Fin 8 → Bool) (stk : Fin 10 → List Bool) (ht : stk 8 = []) :
    Eval (copy src dst) (7*(stk src).length+5) ⟨r,stk⟩
      ⟨readRegs r 0 3 none,copyStacks src dst stk⟩ := by
  apply Eval.call
  have he := halt_after_trace _
    (copyProgram_trace src dst 8 (0 : Fin 8) 3 hsd hst htd (by decide) r stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC,copyResult,copyProgram,Nat.add_assoc] using he

/-- An actual preserving Boolean correction test. Its result is a Boolean
register, so the following conditional does not inspect a coefficient low bit. -/
theorem command_eval (r : Fin 8 → Bool) (a E H : List Bool)
    (haE : a.length=E.length) (haH : a.length=H.length) :
    ∃ rf, Eval command (29*a.length+19) (data r a E H [] [] [] [] [] [])
      (data rf a E H [] [] [] [] [] []) ∧ rf 6=LeafWeightProgram.good a E H := by
  have e1 := copy_eval 0 5 (by decide) (by decide) (by decide) r
    (tapes a E H [] [] [] [] [] []) rfl
  change Eval (copy 0 5) (7*a.length+5)
    (data r a E H [] [] [] [] [] [])
    ⟨readRegs r 0 3 none,Function.update (tapes a E H [] [] [] [] [] []) 5 (a++[])⟩ at e1
  rw [List.append_nil,update5] at e1
  let r1 := readRegs r 0 3 none
  have e2 := copy_eval 1 6 (by decide) (by decide) (by decide) r1
    (tapes a E H [] [] a [] [] []) rfl
  change Eval (copy 1 6) (7*E.length+5)
    (data r1 a E H [] [] a [] [] [])
    ⟨readRegs r1 0 3 none,Function.update (tapes a E H [] [] a [] [] []) 6 (E++[])⟩ at e2
  rw [List.append_nil,update6] at e2
  let r2 := readRegs r1 0 3 none
  have e3 := copy_eval 2 7 (by decide) (by decide) (by decide) r2
    (tapes a E H [] [] a E [] []) rfl
  change Eval (copy 2 7) (7*H.length+5)
    (data r2 a E H [] [] a E [] [])
    ⟨readRegs r2 0 3 none,Function.update (tapes a E H [] [] a E [] []) 7 (H++[])⟩ at e3
  rw [List.append_nil,update7] at e3
  obtain ⟨rf,es,hs⟩ := scan_eval (readRegs r2 0 3 none) a E H [] [] [] haE haH
  refine ⟨rf,?_,hs⟩
  have he := e1.seq (e2.seq (e3.seq es))
  convert he using 1
  · rfl
  · omega

def program := compiled command 0 0

theorem run_space (r : Fin 8 → Bool) (a E H : List Bool)
    (haE : a.length=E.length) (haH : a.length=H.length) :
    ∃ rf, Trace program (29*a.length+20)
      ((data r a E H [] [] [] [] [] []).withPC (some program.entry))
      ((data rf a E H [] [] [] [] [] []).withPC none) ∧
      rf 6=LeafWeightProgram.good a E H ∧
      ∀ j ≤ 29*a.length+20, ∀ c, Trace program j
        ((data r a E H [] [] [] [] [] []).withPC (some program.entry)) c →
        dataBits c ≤ 32*a.length+20 := by
  obtain ⟨rf,he,hv⟩ := command_eval r a E H haE haH
  refine ⟨rf,by simpa [program,Nat.add_assoc] using compiled_halt_trace he 0 0,hv,?_⟩
  intro j hj c hc
  have hg := trace_dataBits program hc
  have hi : dataBits ((data r a E H [] [] [] [] [] []).withPC (some program.entry)) =
      3*a.length := by
    simp [dataBits,stackBits,tapes,
      Fin.sum_univ_succ,←haE,←haH]
    omega
  rw [hi] at hg
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.CorrectionGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 16 32
abbrev Code := Cmd 16 32

def state (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool) : Data :=
  ⟨regs,![W,[],[],[],[],[],[],[],[],[],[],[],bits,[],key,words (rows.map words),
    wanted,E,H,[],[],[],[],[],[],[],[],[],[],[],[],[]]⟩

def keyRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def keyStacks : Fin 16 → Fin 32 := Fin.castAdd 16
def keyCall : Code := .call (ProgramLinking.liftProgram
  AttainedSignatureProgram.program keyRegisters keyStacks)

def equalityRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
def equalityStacks : Fin 6 → Fin 32 := ![14,1,16,3,4,5]
def equalityCall : Code := .call (ProgramLinking.liftProgram
  AttainedSignatureProgram.KeyEquality.program equalityRegisters equalityStacks)

def correctionStacks : Fin 10 → Fin 32 := ![12,17,18,19,20,5,6,7,8,21]
def correctionCall : Code := .call (ProgramLinking.liftProgram
  CorrectionGate.program keyRegisters correctionStacks)

def clearKey : Code := .call (StackRoutines.clearProgram 14 (0:Fin 16) 1)

/-- Every candidate pays for the complete key comparison and correction scan.
Only the final Boolean register selects whether its factor value is added. -/
def command : Code := .seq keyCall (.seq equalityCall
  (.seq (.base (.atom (.copy 15 4))) (.seq correctionCall
    (.seq (.base (.atom (.band 15 15 6))) clearKey))))

theorem keyCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool)
    (hlen : ∀ row ∈ rows, row.length=bits.length) :
    ∃ n ≤ AttainedSignatureProgram.cost W bits rows+1, ∃ out,
      Eval keyCall n (state regs W bits rows key wanted E H)
        (state out W bits rows (signatureValue W bits rows++key) wanted E H) := by
  let a := state regs W bits rows key wanted E H
  have hr : Function.Injective keyRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective keyStacks := Fin.castAdd_injective _ _
  have hp : projectState keyRegisters keyStacks a =
      AttainedSignatureProgram.state (regs ∘ keyRegisters) W bits rows key := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> rfl
  obtain ⟨n,hn,out,he⟩ := AttainedSignatureProgram.command_eval
    (regs ∘ keyRegisters) W bits rows key hlen
  rw [←hp] at he
  have hc := eval_call_from_state AttainedSignatureProgram.program
    keyRegisters keyStacks a hr hs (compiled_halt_trace he 12 14)
  let e := embedState keyRegisters keyStacks a
    (AttainedSignatureProgram.state out W bits rows (signatureValue W bits rows++key))
  have heq : e = state e.regs W bits rows (signatureValue W bits rows++key) wanted E H := by
    apply embedState_eq_of_ports keyRegisters keyStacks a _ _ hr hs
    · intro i; exact embedState_register keyRegisters keyStacks a _ hr i
    · intro i hi; exact embedState_register_frame keyRegisters keyStacks a _ i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have hil : 16 ≤ i.val := by
        by_contra h
        exact hi ⟨⟨i.val,by omega⟩,Fin.ext rfl⟩
      fin_cases i <;> simp_all [state,a]
  change Eval keyCall (n+1) a e at hc
  rw [heq] at hc
  exact ⟨n+1,Nat.add_le_add_right hn 1,e.regs,hc⟩

theorem equalityCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool) :
    ∃ n ≤ 18*key.length+9*wanted.length+26, ∃ out,
      Eval equalityCall n (state regs W bits rows key wanted E H)
        (state out W bits rows key wanted E H) ∧ out 4=decide (key=wanted) := by
  let a := state regs W bits rows key wanted E H
  have hr : Function.Injective equalityRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective equalityStacks := by decide
  have hp : projectState equalityRegisters equalityStacks a =
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ equalityRegisters) key [] wanted [] [] [] := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> rfl
  obtain ⟨n,hn,out,he,hanswer⟩ :=
    AttainedSignatureProgram.KeyEquality.command_eval (regs ∘ equalityRegisters) key wanted []
  rw [←hp] at he
  have hc := eval_call_from_state AttainedSignatureProgram.KeyEquality.program
    equalityRegisters equalityStacks a hr hs (compiled_halt_trace he 0 0)
  let e := embedState equalityRegisters equalityStacks a
    (OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState out key [] wanted [] [] [])
  have heq : e = state e.regs W bits rows key wanted E H := by
    apply embedState_eq_of_ports equalityRegisters equalityStacks a _ _ hr hs
    · intro i; exact embedState_register equalityRegisters equalityStacks a _ hr i
    · intro i hi; exact embedState_register_frame equalityRegisters equalityStacks a _ i hi
    · intro i; fin_cases i <;> rfl
    · intro i _; rfl
  have ha : e.regs 4=decide (key=wanted) := by
    change e.regs (equalityRegisters 4)=_
    rw [embedState_register equalityRegisters equalityStacks a _ hr]
    exact hanswer
  change Eval equalityCall (n+1) a e at hc
  rw [heq] at hc
  exact ⟨n+1,by omega,e.regs,hc,ha⟩

theorem correctionCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool)
    (hE : bits.length=E.length) (hH : bits.length=H.length) :
    ∃ out, Eval correctionCall (29*bits.length+20)
      (state regs W bits rows key wanted E H) (state out W bits rows key wanted E H) ∧
      out 6=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H ∧ out 15=regs 15 := by
  let a := state regs W bits rows key wanted E H
  have hr : Function.Injective keyRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective correctionStacks := by decide
  have hp : projectState keyRegisters correctionStacks a =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.Native.data (regs ∘ keyRegisters)
        bits E H [] [] [] [] [] [] := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> rfl
  obtain ⟨out,he,hanswer⟩ := CorrectionGate.command_eval (regs ∘ keyRegisters) bits E H hE hH
  rw [←hp] at he
  have hc := eval_call_from_state CorrectionGate.program keyRegisters correctionStacks a hr hs
    (compiled_halt_trace he 0 0)
  let e := embedState keyRegisters correctionStacks a
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.Native.data out bits E H [] [] [] [] [] [])
  have heq : e = state e.regs W bits rows key wanted E H := by
    apply embedState_eq_of_ports keyRegisters correctionStacks a _ _ hr hs
    · intro i; exact embedState_register keyRegisters correctionStacks a _ hr i
    · intro i hi; exact embedState_register_frame keyRegisters correctionStacks a _ i hi
    · intro i; fin_cases i <;> rfl
    · intro i _; rfl
  have ha : e.regs 6=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H := by
    change e.regs (keyRegisters 6)=_
    rw [embedState_register keyRegisters correctionStacks a _ hr]
    exact hanswer
  have hf : e.regs 15=regs 15 := by
    exact embedState_register_frame keyRegisters correctionStacks a _ 15 (by
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      simp [keyRegisters] at hv
      omega)
  change Eval correctionCall (29*bits.length+19+1) a e at hc
  rw [heq] at hc
  exact ⟨e.regs,by simpa [Nat.add_assoc] using hc,ha,hf⟩

def budget (W bits : List Bool) (rows : List (List (List Bool))) (wanted : List Bool) : ℕ :=
  AttainedSignatureProgram.cost W bits rows+20*(signatureValue W bits rows).length+
    9*wanted.length+29*bits.length+52

theorem command_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (wanted E H : List Bool)
    (hlen : ∀ row ∈ rows, row.length=bits.length)
    (hE : bits.length=E.length) (hH : bits.length=H.length) :
    ∃ n ≤ budget W bits rows wanted, ∃ out,
      Eval command n (state regs W bits rows [] wanted E H)
        (state out W bits rows [] wanted E H) ∧
      out 15=(decide (signatureValue W bits rows=wanted) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H) := by
  obtain ⟨nk,hnk,rk,hk⟩ := keyCall_eval regs W bits rows [] wanted E H hlen
  simp only [List.append_nil] at hk
  obtain ⟨ne,hne,re,he,hanswer⟩ :=
    equalityCall_eval rk W bits rows (signatureValue W bits rows) wanted E H
  let rc := Function.update re 15 (re 4)
  have hcopy : Eval (.base (.atom (.copy 15 4))) 1
      (state re W bits rows (signatureValue W bits rows) wanted E H)
      (state rc W bits rows (signatureValue W bits rows) wanted E H) :=
    .base (.atom _ _)
  obtain ⟨rr,hr,hcorr,hframe⟩ :=
    correctionCall_eval rc W bits rows (signatureValue W bits rows) wanted E H hE hH
  let rb := Function.update rr 15 (rr 15 && rr 6)
  have hband : Eval (.base (.atom (.band 15 15 6))) 1
      (state rr W bits rows (signatureValue W bits rows) wanted E H)
      (state rb W bits rows (signatureValue W bits rows) wanted E H) :=
    .base (.atom _ _)
  let rf := readRegs rb 0 1 none
  have hclear : Eval clearKey (2*(signatureValue W bits rows).length+3)
      (state rb W bits rows (signatureValue W bits rows) wanted E H)
      (state rf W bits rows [] wanted E H) := by
    have hc : Eval clearKey _
        (state rb W bits rows (signatureValue W bits rows) wanted E H)
        ⟨rf,StackRoutines.clearStacks 14
          (state rb W bits rows (signatureValue W bits rows) wanted E H).stacks⟩ :=
      .call _ (ListRegisterProgram.clear_run 14 0 1 rb _)
    convert hc using 1
    · simp [state]
    · apply congrArg (StructuredProgram.State.mk rf)
      funext i; fin_cases i <;> simp [state,StackRoutines.clearStacks]
  refine ⟨_,?_,rf,hk.seq (he.seq (hcopy.seq (hr.seq (hband.seq hclear)))),?_⟩
  · dsimp [budget]
    omega
  · simp [rf,rb,rc,readRegs,hcorr,hframe,hanswer]

/-- Both losing and successful candidates satisfy the same fixed polynomial
bound, including every full raw matrix row and both complete signature words. -/
theorem budget_signature_le (W bits representative : List Bool)
    (rows : List (List (List Bool))) (B : ℕ)
    (hlen : ∀ row ∈ rows, row.length=bits.length)
    (hrep : representative.length=bits.length)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length≤B) :
    budget W bits rows (signatureValue W representative rows) ≤
      7*(words (rows.map words)).length+
      rows.length*(signatureRowBound W bits.length B+2)+
      29*(rows.length*(2*(widthBound W bits.length B+1)+1))+29*bits.length+60 := by
  have hc := AttainedSignatureProgram.cost_le W bits rows B hlen hwidth
  have hk := signatureValue_length_bound W bits rows B hlen hwidth
  have hr := signatureValue_length_bound W representative rows B
    (by intro row hrow; exact (hlen row hrow).trans hrep.symm) hwidth
  rw [hrep] at hr
  dsimp [budget]
  omega

def program := compiled command 12 12

/-- The complete key, E mask and head mask are tested by a fixed actual
program. Every temporary is cleared before the next candidate is visited. -/
theorem run_space (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (wanted E H : List Bool)
    (hlen : ∀ row ∈ rows, row.length=bits.length)
    (hE : bits.length=E.length) (hH : bits.length=H.length) :
    ∃ steps ≤ budget W bits rows wanted+1, ∃ out,
      Trace program steps
        ((state regs W bits rows [] wanted E H).withPC (some program.entry))
        ((state out W bits rows [] wanted E H).withPC none) ∧
      out 15=(decide (signatureValue W bits rows=wanted) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H) ∧
      ∀ j ≤ steps, ∀ c, Trace program j
        ((state regs W bits rows [] wanted E H).withPC (some program.entry)) c →
        dataBits c ≤ W.length+bits.length+(words (rows.map words)).length+
          wanted.length+E.length+H.length+budget W bits rows wanted+1 := by
  obtain ⟨steps,hsteps,out,he,hv⟩ := command_eval regs W bits rows wanted E H hlen hE hH
  refine ⟨steps+1,Nat.add_le_add_right hsteps 1,out,
    compiled_halt_trace he 12 12,hv,?_⟩
  intro j hj c hc
  have hg := trace_dataBits program hc
  have hi : dataBits ((state regs W bits rows [] wanted E H).withPC (some program.entry)) =
      W.length+bits.length+(words (rows.map words)).length+wanted.length+E.length+H.length := by
    simp [dataBits,stackBits,state,Fin.sum_univ_succ,Nat.add_assoc]
  rw [hi] at hg
  omega

/-- Byte equality is exactly equality of the full integer signature, and the
other Boolean conjunct is exactly the original-coordinate correction test. -/
theorem flag_exact_iff {h d : ℕ} {G : Type*} [DecidableEq G]
    (W : List Bool) (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (a b : Fin h → Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ)+A j i)
    (E : Finset (Fin h)) (head : Fin h → G) (g : G) :
    (decide (signatureValue W (List.ofFn a) (List.ofFn (fun j => List.ofFn (c j))) =
      signatureValue W (List.ofFn b) (List.ofFn (fun j => List.ofFn (c j)))) &&
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (List.ofFn a)
        (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits ⟨E⟩)
        (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.headBits head g)) = true ↔
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A a =
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A b ∧
      ∀ i ∈ E, head i=g → a i=true := by
  rw [Bool.and_eq_true,decide_eq_true_eq,
    AttainedSignatureProgram.key_eq_iff W c A a b hc,
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.selected_iff]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def copy (src dst : Fin 896) : Code := .call (copyProgram src dst 31 (0:Fin 40) 1)
def clear (src : Fin 896) : Code := .call (clearProgram src (0:Fin 40) 1)
def copyState (d : Data) (src dst : Fin 896) : Data :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩
def clearState (d : Data) (src : Fin 896) : Data :=
  ⟨readRegs d.regs 0 1 none,clearStacks src d.stacks⟩

def registers : Fin 16 → Fin 40 := Fin.castAdd 24
def stackMap : Fin 32 → Fin 896 := Fin.castAdd 864

def callGate : Code := .call (ProgramLinking.liftProgram HeadGate.program registers stackMap)
def stage : Code := .seq (copy 864 0) (.seq (copy 859 12) (.seq (copy 865 15)
  (.seq (copy 866 16) (.seq (copy 867 17) (copy 868 18)))))
def cleanup : Code := .seq (clear 0) (.seq (clear 12) (.seq (clear 15)
  (.seq (clear 16) (.seq (clear 17) (clear 18)))))
def command : Code := .seq stage (.seq callGate cleanup)

def sourceLength (d : Data) : ℕ :=
  (d.stacks 864).length+(d.stacks 859).length+(d.stacks 865).length+
    (d.stacks 866).length+(d.stacks 867).length+(d.stacks 868).length

def staged (d : Data) : Data :=
  copyState (copyState (copyState (copyState (copyState (copyState d 864 0)
    859 12) 865 15) 866 16) 867 17) 868 18

def cleaned (d : Data) : Data :=
  clearState (clearState (clearState (clearState (clearState (clearState d 0)
    12) 15) 16) 17) 18

theorem copy_eval (d : Data) (src dst : Fin 896)
    (hsd : src≠dst) (hst : src≠31) (htd : (31:Fin 896)≠dst) (ht : d.stacks 31=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copyState d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

theorem clear_eval (d : Data) (src : Fin 896) :
    Eval (clear src) (2*(d.stacks src).length+3) d (clearState d src) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

theorem stage_eval (d : Data) (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[]) :
    Eval stage (7*sourceLength d+30) d (staged d) := by
  have h31 : d.stacks 31=[] := hclean 31
  let d1 := copyState d 864 0
  let d2 := copyState d1 859 12
  let d3 := copyState d2 865 15
  let d4 := copyState d3 866 16
  let d5 := copyState d4 867 17
  have h1 := copy_eval d 864 0 (by decide) (by decide) (by decide) h31
  have h2 := copy_eval d1 859 12 (by decide) (by decide) (by decide)
    (by simp [d1,copyState,copyStacks,h31])
  have h3 := copy_eval d2 865 15 (by decide) (by decide) (by decide)
    (by simp [d2,d1,copyState,copyStacks,h31])
  have h4 := copy_eval d3 866 16 (by decide) (by decide) (by decide)
    (by simp [d3,d2,d1,copyState,copyStacks,h31])
  have h5 := copy_eval d4 867 17 (by decide) (by decide) (by decide)
    (by simp [d4,d3,d2,d1,copyState,copyStacks,h31])
  have h6 := copy_eval d5 868 18 (by decide) (by decide) (by decide)
    (by simp [d5,d4,d3,d2,d1,copyState,copyStacks,h31])
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  · rfl
  · simp [sourceLength,d5,d4,d3,d2,d1,copyState,copyStacks]
    omega
  · rfl

theorem stage_project (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words)) :
    projectState registers stackMap (staged d) =
      HeadGate.state ((staged d).regs ∘ registers) (d.stacks 864) (d.stacks 859) rows []
        (d.stacks 866) (d.stacks 867) (d.stacks 868) := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  have hi := hclean i
  fin_cases i <;>
    simp_all [stackMap,staged,copyState,copyStacks]

theorem stage_high (d : Data) (i : Fin 896) (hi : 32 ≤ i.val) :
    (staged d).stacks i=d.stacks i := by
  have h0 : i≠0 := by intro h; subst i; omega
  have h12 : i≠12 := by intro h; subst i; omega
  have h15 : i≠15 := by intro h; subst i; omega
  have h16 : i≠16 := by intro h; subst i; omega
  have h17 : i≠17 := by intro h; subst i; omega
  have h18 : i≠18 := by intro h; subst i; omega
  simp [staged,copyState,copyStacks,h0,h12,h15,h16,h17,h18]

def lowLength (d : Data) : ℕ :=
  (d.stacks 0).length+(d.stacks 12).length+(d.stacks 15).length+
    (d.stacks 16).length+(d.stacks 17).length+(d.stacks 18).length

theorem cleanup_eval (d : Data) :
    Eval cleanup (2*lowLength d+18) d (cleaned d) := by
  let d1 := clearState d 0
  let d2 := clearState d1 12
  let d3 := clearState d2 15
  let d4 := clearState d3 16
  let d5 := clearState d4 17
  have h1 := clear_eval d 0
  have h2 := clear_eval d1 12
  have h3 := clear_eval d2 15
  have h4 := clear_eval d3 16
  have h5 := clear_eval d4 17
  have h6 := clear_eval d5 18
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  · rfl
  · simp [lowLength,d5,d4,d3,d2,d1,clearState,clearStacks]
    omega
  · rfl

theorem cleaned_staged (d : Data) (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[]) :
    (cleaned (staged d)).stacks=d.stacks := by
  funext i
  by_cases hi : i.val < 32
  · obtain ⟨j,rfl⟩ : ∃ j : Fin 32, stackMap j=i := ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    have hh := hclean j
    fin_cases j <;>
      simp_all [stackMap,cleaned,clearState,clearStacks,staged,copyState,copyStacks]
  · have hh : 32 ≤ i.val := by omega
    have h0 : i≠0 := by intro h; subst i; omega
    have h12 : i≠12 := by intro h; subst i; omega
    have h15 : i≠15 := by intro h; subst i; omega
    have h16 : i≠16 := by intro h; subst i; omega
    have h17 : i≠17 := by intro h; subst i; omega
    have h18 : i≠18 := by intro h; subst i; omega
    simp only [cleaned,clearState,clearStacks,Function.update_of_ne h0,
      Function.update_of_ne h12,Function.update_of_ne h15,Function.update_of_ne h16,
      Function.update_of_ne h17,Function.update_of_ne h18]
    exact stage_high d i hh

theorem staged_lowLength (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words)) :
    lowLength (staged d)=sourceLength d := by
  have hp := stage_project d rows hclean hmatrix
  have h0 := congrArg (fun a => a.stacks (0:Fin 32)) hp
  have h12 := congrArg (fun a => a.stacks (12:Fin 32)) hp
  have h15 := congrArg (fun a => a.stacks (15:Fin 32)) hp
  have h16 := congrArg (fun a => a.stacks (16:Fin 32)) hp
  have h17 := congrArg (fun a => a.stacks (17:Fin 32)) hp
  have h18 := congrArg (fun a => a.stacks (18:Fin 32)) hp
  simp [projectState,stackMap,HeadGate.state] at h0 h12 h15 h16 h17 h18
  simp [lowLength,sourceLength,h0,h12,h15,h16,h17,h18,hmatrix]

theorem command_eval_frame (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length=(d.stacks 859).length)
    (hE : (d.stacks 859).length=(d.stacks 867).length)
    (hH : (d.stacks 859).length=(d.stacks 868).length) :
    ∃ n ≤ HeadGate.budget (d.stacks 864) (d.stacks 859) rows (d.stacks 866)+
      9*sourceLength d+49, ∃ out,
      Eval command n d ⟨out,d.stacks⟩ ∧
      out 15=(decide (signatureValue (d.stacks 864) (d.stacks 859) rows=d.stacks 866) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (d.stacks 859) (d.stacks 867) (d.stacks 868)) ∧
      ∀ i : Fin 40, 16 ≤ i.val → out i=d.regs i := by
  have hp := stage_project d rows hclean hmatrix
  have hr : Function.Injective registers := Fin.castAdd_injective _ _
  have hs : Function.Injective stackMap := Fin.castAdd_injective _ _
  obtain ⟨n,hn,out,he,hv⟩ := HeadGate.command_eval ((staged d).regs ∘ registers)
    (d.stacks 864) (d.stacks 859) rows (d.stacks 866) (d.stacks 867) (d.stacks 868) hlen hE hH
  rw [←hp] at he
  have hc := eval_call_from_state HeadGate.program registers stackMap (staged d) hr hs
    (compiled_halt_trace he 12 12)
  let e := embedState registers stackMap (staged d)
    (HeadGate.state out (d.stacks 864) (d.stacks 859) rows []
      (d.stacks 866) (d.stacks 867) (d.stacks 868))
  have heq : e=⟨e.regs,(staged d).stacks⟩ := by
    apply embedState_eq_of_ports registers stackMap (staged d) _ _ hr hs
    · intro i; exact embedState_register registers stackMap (staged d) _ hr i
    · intro i hi; exact embedState_register_frame registers stackMap (staged d) _ i hi
    · intro i
      exact congrArg (fun a => a.stacks i) hp
    · intro i _; rfl
  have hstacks := congrArg (fun a : Data => a.stacks) heq
  change e.stacks=(staged d).stacks at hstacks
  have hflag : e.regs 15=out 15 :=
    embedState_register registers stackMap (staged d) _ hr 15
  change Eval callGate (n+1) (staged d) e at hc
  have hcleanup := cleanup_eval e
  have hlenE : lowLength e=sourceLength d := by
    simpa only [lowLength,hstacks] using staged_lowLength d rows hclean hmatrix
  rw [hlenE] at hcleanup
  have hfinal : (cleaned e).stacks=d.stacks := by
    have h := cleaned_staged d hclean
    simpa only [cleaned,clearState,clearStacks,hstacks] using h
  have hfinalFlag : (cleaned e).regs 15=out 15 := by
    simpa [cleaned,clearState,readRegs] using hflag
  have hframe : ∀ i : Fin 40, 16 ≤ i.val → (cleaned e).regs i=d.regs i := by
    intro i hi
    have h0 : i≠0 := by intro h; subst i; omega
    have h1 : i≠1 := by intro h; subst i; omega
    have hout : i ∉ Set.range registers := by
      rintro ⟨j,hj⟩
      have hjv := congrArg Fin.val hj
      simp only [registers,Fin.val_castAdd] at hjv
      omega
    have hh := embedState_register_frame registers stackMap (staged d)
      (HeadGate.state out (d.stacks 864) (d.stacks 859) rows []
        (d.stacks 866) (d.stacks 867) (d.stacks 868)) i hout
    change e.regs i=(staged d).regs i at hh
    simpa [cleaned,clearState,staged,copyState,readRegs,h0,h1] using hh
  have hall := (stage_eval d hclean).seq (hc.seq hcleanup)
  refine ⟨7*sourceLength d+30+(n+1+(2*sourceLength d+18)),
    by omega,(cleaned e).regs,?_,hfinalFlag.trans hv,hframe⟩
  convert hall using 1
  · rfl
  · exact congrArg (StructuredProgram.State.mk (cleaned e).regs) hfinal.symm

/-- The concrete leaf-ABI wrapper reads cursor859 and persistent metadata864..868,
clears its low scratch bank, and preserves every stack of the caller. -/
theorem command_eval (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length=(d.stacks 859).length)
    (hE : (d.stacks 859).length=(d.stacks 867).length)
    (hH : (d.stacks 859).length=(d.stacks 868).length) :
    ∃ n ≤ HeadGate.budget (d.stacks 864) (d.stacks 859) rows (d.stacks 866)+
      9*sourceLength d+49, ∃ out,
      Eval command n d ⟨out,d.stacks⟩ ∧
      out 15=(decide (signatureValue (d.stacks 864) (d.stacks 859) rows=d.stacks 866) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (d.stacks 859) (d.stacks 867) (d.stacks 868)) := by
  obtain ⟨n,hn,out,he,hv,_⟩ := command_eval_frame d rows hclean hmatrix hlen hE hH
  exact ⟨n,hn,out,he,hv⟩

def program := compiled command 859 859

/-- One actual fixed program tests a cursor without changing any caller stack.
Its all-prefix bound includes the entire persistent query state. -/
theorem run_space (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length=(d.stacks 859).length)
    (hE : (d.stacks 859).length=(d.stacks 867).length)
    (hH : (d.stacks 859).length=(d.stacks 868).length) :
    let budget := HeadGate.budget (d.stacks 864) (d.stacks 859) rows (d.stacks 866)+
      9*sourceLength d+50
    ∃ n ≤ budget, ∃ out,
      Trace program n (d.withPC (some program.entry))
        ((⟨out,d.stacks⟩ : Data).withPC none) ∧
      out 15=(decide (signatureValue (d.stacks 864) (d.stacks 859) rows=d.stacks 866) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (d.stacks 859) (d.stacks 867) (d.stacks 868)) ∧
      ∀ j ≤ n, ∀ c, Trace program j (d.withPC (some program.entry)) c →
        dataBits c ≤ stackBits d.stacks+budget := by
  dsimp only
  obtain ⟨n,hn,out,he,hv⟩ := command_eval d rows hclean hmatrix hlen hE hH
  refine ⟨n+1,by omega,out,compiled_halt_trace he 859 859,hv,?_⟩
  intro j hj c hc
  have hg := trace_dataBits program hc
  change dataBits c ≤ stackBits d.stacks+j at hg
  omega

/-- One actual fixed program tests a cursor without changing any caller stack.
Its all-prefix bound includes the entire persistent query state. -/
theorem run_space_frame (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length=(d.stacks 859).length)
    (hE : (d.stacks 859).length=(d.stacks 867).length)
    (hH : (d.stacks 859).length=(d.stacks 868).length) :
    let budget := HeadGate.budget (d.stacks 864) (d.stacks 859) rows (d.stacks 866)+
      9*sourceLength d+50
    ∃ n ≤ budget, ∃ out,
      Trace program n (d.withPC (some program.entry))
        ((⟨out,d.stacks⟩ : Data).withPC none) ∧
      out 15=(decide (signatureValue (d.stacks 864) (d.stacks 859) rows=d.stacks 866) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (d.stacks 859) (d.stacks 867) (d.stacks 868)) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out i=d.regs i) ∧
      ∀ j ≤ n, ∀ c, Trace program j (d.withPC (some program.entry)) c →
        dataBits c ≤ stackBits d.stacks+budget := by
  dsimp only
  obtain ⟨n,hn,out,he,hv,hframe⟩ := command_eval_frame d rows hclean hmatrix hlen hE hH
  refine ⟨n+1,by omega,out,compiled_halt_trace he 859 859,hv,hframe,?_⟩
  intro j hj c hc
  have hg := trace_dataBits program hc
  change dataBits c ≤ stackBits d.stacks+j at hg
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def widthPolynomial (B : ℕ) : ℕ := 1+B*(B+1+B)
def rowPolynomial (B : ℕ) : ℕ :=
  9*(B*(2*B+1))+7+(7*B+5)+2+
    ((B+1)*(200*(widthPolynomial B+2)^2+34)+9*widthPolynomial B+22+1)+
      8*(widthPolynomial B+1)+8
/-- A fixed degree-six polynomial charges the full raw matrix and key words. -/
def gatePolynomial (B : ℕ) : ℕ :=
  7*B+B*(rowPolynomial B+2)+20*(B*(2*(widthPolynomial B+1)+1))+38*B+60

theorem widthBound_le_polynomial (W : List Bool) (h B : ℕ)
    (hW : W.length≤B) (hh : h≤B) : widthBound W h B≤widthPolynomial B := by
  dsimp [widthBound,widthPolynomial]
  gcongr

theorem rowBound_le_polynomial (W bits : List Bool) (B : ℕ)
    (hW : W.length≤B) (hh : bits.length≤B) :
    signatureRowBound W bits.length B≤rowPolynomial B := by
  have hw := widthBound_le_polynomial W bits.length B hW hh
  dsimp [signatureRowBound,rowCostBound,rowPolynomial]
  gcongr

/-- Uniform over every candidate, including losing checks. The desired key
may be any retained word; the current complete integer key is computed and charged. -/
theorem budget_uniform (W bits wanted : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hlen : ∀ row ∈ rows,row.length=bits.length)
    (hwidth : ∀ row ∈ rows,∀ x ∈ row,x.length≤B)
    (hW : W.length≤B) (hh : bits.length≤B) (hwanted : wanted.length≤B)
    (hmatrix : (words (rows.map words)).length≤B) (hrows : rows.length≤B) :
    budget W bits rows wanted≤gatePolynomial B := by
  have hc := AttainedSignatureProgram.cost_le W bits rows B hlen hwidth
  have hk := signatureValue_length_bound W bits rows B hlen hwidth
  have hr := rowBound_le_polynomial W bits B hW hh
  have hw := widthBound_le_polynomial W bits.length B hW hh
  calc
    budget W bits rows wanted ≤
      7*(words (rows.map words)).length+rows.length*(signatureRowBound W bits.length B+2)+
        20*(rows.length*(2*(widthBound W bits.length B+1)+1))+
          9*wanted.length+29*bits.length+60 := by
      dsimp [budget]
      omega
    _ ≤ gatePolynomial B := by
      dsimp [gatePolynomial]
      calc
        _ ≤ 7*B+B*(rowPolynomial B+2)+20*(B*(2*(widthPolynomial B+1)+1))+
          9*B+29*B+60 := by gcongr
        _ = _ := by omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
/-- A simple monomial envelope with a degree independent of every input. -/
theorem gatePolynomial_le (B : ℕ) : gatePolynomial B≤15000*(B+1)^6 := by
  dsimp [gatePolynomial,rowPolynomial,widthPolynomial]
  nlinarith only [Nat.zero_le B,Nat.zero_le (B^2),Nat.zero_le (B^3),
    Nat.zero_le (B^4),Nat.zero_le (B^5),Nat.zero_le (B^6)]
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

def bodyPolynomial (B : ℕ) : ℕ := HeadGate.gatePolynomial B+62*B+58

theorem sourceLength_le (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length≤B) : sourceLength a≤6*B := by
  have h0 := ha 864; have h1 := ha 859; have h2 := ha 865
  have h3 := ha 866; have h4 := ha 867; have h5 := ha 868
  dsimp [sourceLength]
  omega

/-- Every candidate, successful or losing, is charged within one fixed
polynomial plus the separately charged accepted factor calculation. -/
theorem bodyBudget_uniform (a : Data) (rows : List (List (List Bool))) (B acceptedCost : ℕ)
    (hmatrix : a.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows,row.length=(a.stacks 859).length)
    (hwidth : ∀ row ∈ rows,∀ x ∈ row,x.length≤B)
    (hrows : rows.length≤B) (ha : ∀ i, (a.stacks i).length≤B) :
    HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866)+
      9*sourceLength a+acceptedCost+8*(a.stacks 859).length+58≤
      bodyPolynomial B+acceptedCost := by
  have hm : (words (rows.map words)).length≤B := by rw [←hmatrix]; exact ha 865
  have hg := HeadGate.budget_uniform (a.stacks 864) (a.stacks 859) (a.stacks 866) rows B
    hlen hwidth (ha 864) (ha 859) (ha 866) hm hrows
  have hs := sourceLength_le a B ha
  have hh := ha 859
  dsimp [bodyPolynomial]
  omega

theorem bodyPolynomial_le (B : ℕ) : bodyPolynomial B≤16000*(B+1)^6 := by
  have hg := HeadGate.gatePolynomial_le B
  dsimp [bodyPolynomial]
  nlinarith only [hg,Nat.zero_le B,Nat.zero_le (B^2),Nat.zero_le (B^3),
    Nat.zero_le (B^4),Nat.zero_le (B^5),Nat.zero_le (B^6)]
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram


theorem seq_space {c e : Code} {n m B : ℕ} {a b d : Data}
    (hc : Eval c n a b) (he : Eval e m b d)
    (hcb : (∀ q z, q ≤ n → Trace (compiled c 860 860) q
      (a.withPC (some (compiled c 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) (heb : (∀ q z, q ≤ m → Trace (compiled e 860 860) q
      (b.withPC (some (compiled e 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) :
    (∀ q z, q ≤ (n+m) → Trace (compiled (.seq c e) 860 860) q
      (a.withPC (some (compiled (.seq c e) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) :=
  StructuredSpace.sequence_stack_bound hc he 860 860 hcb heb
    (compiled (.seq c e) 860 860) (siteAddress (.seq c e)) (exitAddress (.seq c e))
    (compiled_site (.seq c e) 860 860)

theorem copy_space {n B : ℕ} {a b : Data} (src dst : Fin 896)
    (he : Eval (copy src dst) n a b) (hsd : src≠dst) (hst : src≠31)
    (htd : (31:Fin 896)≠dst) (hd : a.stacks dst=[]) (ht : a.stacks 31=[])
    (ha : ∀ i, (a.stacks i).length≤B) : (∀ q z, q ≤ n → Trace (compiled (copy src dst) 860 860) q
      (a.withPC (some (compiled (copy src dst) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (copy src dst) 860 860) tr
    intro q z _ hq
    exact CopySpace.copyProgram_no_growth src dst 31 0 1 hsd hst htd rfl hd ht ha hq

theorem clear_space {n B : ℕ} {a b : Data} (src : Fin 896)
    (he : Eval (clear src) n a b) (ha : ∀ i, (a.stacks i).length≤B) :
    (∀ q z, q ≤ n → Trace (compiled (clear src) 860 860) q
      (a.withPC (some (compiled (clear src) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (clear src) 860 860) tr
    intro q z _ hq i
    exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le src 0 1 hq i).trans (ha i)

theorem copyState_bound (a : Data) (src dst : Fin 896) {B : ℕ}
    (hd : a.stacks dst=[]) (ha : ∀ i, (a.stacks i).length≤B) :
    ∀ i, ((copyState a src dst).stacks i).length≤B := by
  intro i
  by_cases hi : i=dst
  · subst i; simpa [copyState,copyStacks,hd] using ha src
  · simpa [copyState,copyStacks,hi] using ha i

theorem clearState_bound (a : Data) (src : Fin 896) {B : ℕ}
    (ha : ∀ i, (a.stacks i).length≤B) :
    ∀ i, ((clearState a src).stacks i).length≤B := by
  intro i
  by_cases hi : i=src
  · subst i; simp [clearState,clearStacks]
  · simpa [clearState,clearStacks,hi] using ha i

theorem stage_space (a : Data) {B : ℕ}
    (hclean : ∀ i : Fin 32, a.stacks (stackMap i)=[])
    (ha : ∀ i, (a.stacks i).length≤B) :
    (∀ q z, q ≤ (7*sourceLength a+30) → Trace (compiled stage 860 860) q
      (a.withPC (some (compiled stage 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  have h31 : a.stacks 31=[] := hclean 31
  let a1 := copyState a 864 0
  let a2 := copyState a1 859 12
  let a3 := copyState a2 865 15
  let a4 := copyState a3 866 16
  let a5 := copyState a4 867 17
  have h0 : a.stacks 0=[] := hclean 0
  have h12 : a1.stacks 12=[] := by simpa [a1,copyState,copyStacks,stackMap] using hclean 12
  have h15 : a2.stacks 15=[] := by simpa [a2,a1,copyState,copyStacks,stackMap] using hclean 15
  have h16 : a3.stacks 16=[] := by simpa [a3,a2,a1,copyState,copyStacks,stackMap] using hclean 16
  have h17 : a4.stacks 17=[] := by simpa [a4,a3,a2,a1,copyState,copyStacks,stackMap] using hclean 17
  have h18 : a5.stacks 18=[] := by simpa [a5,a4,a3,a2,a1,copyState,copyStacks,stackMap] using hclean 18
  have h1 := copy_eval a 864 0 (by decide) (by decide) (by decide) h31
  have h2 := copy_eval a1 859 12 (by decide) (by decide) (by decide)
    (by simp [a1,copyState,copyStacks,h31])
  have h3 := copy_eval a2 865 15 (by decide) (by decide) (by decide)
    (by simp [a2,a1,copyState,copyStacks,h31])
  have h4 := copy_eval a3 866 16 (by decide) (by decide) (by decide)
    (by simp [a3,a2,a1,copyState,copyStacks,h31])
  have h5 := copy_eval a4 867 17 (by decide) (by decide) (by decide)
    (by simp [a4,a3,a2,a1,copyState,copyStacks,h31])
  have h6 := copy_eval a5 868 18 (by decide) (by decide) (by decide)
    (by simp [a5,a4,a3,a2,a1,copyState,copyStacks,h31])
  have b1 := copyState_bound a 864 0 h0 ha
  have b2 := copyState_bound a1 859 12 h12 b1
  have b3 := copyState_bound a2 865 15 h15 b2
  have b4 := copyState_bound a3 866 16 h16 b3
  have b5 := copyState_bound a4 867 17 h17 b4
  have s1 := copy_space 864 0 h1 (by decide) (by decide) (by decide) h0 h31 ha
  have s2 := copy_space 859 12 h2 (by decide) (by decide) (by decide) h12
    (by simp [a1,copyState,copyStacks,h31]) b1
  have s3 := copy_space 865 15 h3 (by decide) (by decide) (by decide) h15
    (by simp [a2,a1,copyState,copyStacks,h31]) b2
  have s4 := copy_space 866 16 h4 (by decide) (by decide) (by decide) h16
    (by simp [a3,a2,a1,copyState,copyStacks,h31]) b3
  have s5 := copy_space 867 17 h5 (by decide) (by decide) (by decide) h17
    (by simp [a4,a3,a2,a1,copyState,copyStacks,h31]) b4
  have s6 := copy_space 868 18 h6 (by decide) (by decide) (by decide) h18
    (by simp [a5,a4,a3,a2,a1,copyState,copyStacks,h31]) b5
  have hs := seq_space h1 (h2.seq (h3.seq (h4.seq (h5.seq h6)))) s1
    (seq_space h2 (h3.seq (h4.seq (h5.seq h6))) s2
      (seq_space h3 (h4.seq (h5.seq h6)) s3
        (seq_space h4 (h5.seq h6) s4 (seq_space h5 h6 s5 s6))))
  have htime := StreamResources.eval_steps_eq 860 860
    (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))) (stage_eval a hclean)
  simpa only [stage, htime] using hs

theorem cleanup_space (a : Data) {B : ℕ}
    (ha : ∀ i, (a.stacks i).length≤B) :
    (∀ q z, q ≤ (2*lowLength a+18) → Trace (compiled cleanup 860 860) q
      (a.withPC (some (compiled cleanup 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  let a1 := clearState a 0
  let a2 := clearState a1 12
  let a3 := clearState a2 15
  let a4 := clearState a3 16
  let a5 := clearState a4 17
  have h1 := clear_eval a 0
  have h2 := clear_eval a1 12
  have h3 := clear_eval a2 15
  have h4 := clear_eval a3 16
  have h5 := clear_eval a4 17
  have h6 := clear_eval a5 18
  have b1 := clearState_bound a 0 ha
  have b2 := clearState_bound a1 12 b1
  have b3 := clearState_bound a2 15 b2
  have b4 := clearState_bound a3 16 b3
  have b5 := clearState_bound a4 17 b4
  have hs := seq_space h1 (h2.seq (h3.seq (h4.seq (h5.seq h6)))) (clear_space 0 h1 ha)
    (seq_space h2 (h3.seq (h4.seq (h5.seq h6))) (clear_space 12 h2 b1)
      (seq_space h3 (h4.seq (h5.seq h6)) (clear_space 15 h3 b2)
        (seq_space h4 (h5.seq h6) (clear_space 16 h4 b3)
          (seq_space h5 h6 (clear_space 17 h5 b4) (clear_space 18 h6 b5)))))
  have htime := StreamResources.eval_steps_eq 860 860
    (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))) (cleanup_eval a)
  simpa only [cleanup, htime] using hs

private theorem stack_le_dataBits {r s l : ℕ} (z : Cfg r s l) (i : Fin s) :
    (z.stacks i).length≤dataBits z :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((z.stacks j).length)) (Finset.mem_univ i)

/-- The staging and cleanup copy tables preserve the caller envelope exactly;
only the local32 computation needs the separate polynomial allowance. -/
theorem command_space {steps B : ℕ} {a b : Data}
    (he : Eval command steps a b) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, a.stacks (stackMap i)=[])
    (hmatrix : a.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows,row.length=(a.stacks 859).length)
    (hE : (a.stacks 859).length=(a.stacks 867).length)
    (hH : (a.stacks 859).length=(a.stacks 868).length)
    (hframe : ∀ i, (a.stacks i).length≤B)
    (hlocal : sourceLength a+
      HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866)+1≤B) :
    (∀ q z, q ≤ steps → Trace (compiled command 860 860) q
      (a.withPC (some (compiled command 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  have hp := stage_project a rows hclean hmatrix
  have hr : Function.Injective registers := Fin.castAdd_injective _ _
  have hs : Function.Injective stackMap := Fin.castAdd_injective _ _
  obtain ⟨n,hn,out,ht,_,hspace⟩ := HeadGate.run_space ((staged a).regs ∘ registers)
    (a.stacks 864) (a.stacks 859) rows (a.stacks 866) (a.stacks 867) (a.stacks 868)
    hlen hE hH
  let finish := HeadGate.state out (a.stacks 864) (a.stacks 859) rows []
    (a.stacks 866) (a.stacks 867) (a.stacks 868)
  have localBound : ∀ q z, q≤n → Trace HeadGate.program q
      ((projectState registers stackMap (staged a)).withPC (some HeadGate.program.entry)) z →
      ∀ i, (z.stacks i).length≤B := by
    intro q z hq hz i
    rw [hp] at hz
    have hh := hspace q hq z hz
    have hi := stack_le_dataBits z i
    have hb : (a.stacks 864).length+(a.stacks 859).length+
        (words (rows.map words)).length+(a.stacks 866).length+(a.stacks 867).length+
        (a.stacks 868).length+HeadGate.budget (a.stacks 864) (a.stacks 859) rows
        (a.stacks 866)+1≤B := by simpa only [sourceLength,hmatrix] using hlocal
    exact hi.trans (hh.trans hb)
  rw [←hp] at ht
  have hstage := stage_eval a hclean
  have stageBound := stage_space a hclean hframe
  have hmiddle : ∀ i, ((staged a).stacks i).length≤B :=
    stageBound _ _ le_rfl (compiled_trace hstage 860 860)
  have hc := eval_call_from_state HeadGate.program registers stackMap (staged a) hr hs ht
  let e := embedState registers stackMap (staged a) finish
  change Eval callGate n (staged a) e at hc
  have hlift := StructuredSpace.liftProgram_stack_bound HeadGate.program registers stackMap
    ((staged a).withPC none) hr hs ht localBound hmiddle
  have hinit : ProgramLinking.embedCfg registers stackMap id none ((staged a).withPC none)
      ((projectState registers stackMap (staged a)).withPC (some HeadGate.program.entry)) =
      (staged a).withPC (some (ProgramLinking.liftProgram HeadGate.program registers stackMap).entry) := by
    change (embedState registers stackMap (staged a)
      (projectState registers stackMap (staged a))).withPC _ = _
    rw [embedState_project registers stackMap (staged a) hr hs]
    rfl
  rw [hinit] at hlift
  simp only [Nat.max_self] at hlift
  have callBound : (∀ q z, q ≤ n → Trace (compiled callGate 860 860) q
      ((staged a).withPC (some (compiled callGate 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
    cases hc with
    | call routine tr =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site callGate 860 860) tr hlift
  have heBound : ∀ i, (e.stacks i).length≤B :=
    callBound _ _ le_rfl (compiled_trace hc 860 860)
  have hcleanup := cleanup_eval e
  have whole := hstage.seq (hc.seq hcleanup)
  have wholeBound := seq_space hstage (hc.seq hcleanup) stageBound
    (seq_space hc hcleanup callBound (cleanup_space e heBound))
  have heq := StreamResources.eval_steps_eq 860 860 he whole
  rw [heq]
  exact wholeBound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
