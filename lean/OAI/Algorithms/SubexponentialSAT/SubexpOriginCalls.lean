import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginControl
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Concrete extraction, residue conversion and framing calls for the
source-origin mapper. These are measured executions of the fixed programs. -/

namespace SubexponentialSAT.SubexpOriginCalls

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpOriginControl

attribute [local simp] Fin.coe_ofNat_eq_mod

def recordBytes (bits : List Bool) : List Bool := true :: Encoding.frame bits

def lowPort : Fin 14 → Fin 32 := Fin.castAdd 18

def clean (modulus inputWidth width : List Bool) (d : Data) : Prop :=
  (∀ i : Fin 14, d.stacks (lowPort i) =
    if i = 5 then modulus else if i = 10 then inputWidth else if i = 11 then width else []) ∧
  d.stacks 19 = [] ∧ d.stacks 20 = [] ∧ d.stacks 25 = [] ∧ d.stacks 26 = []

def cleared (src : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 32) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  have h : Eval (clear src) (2 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩ :=
    .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)
  simpa only [cleared, StackRoutines.clearStacks] using h

theorem readRegs_high (regs : Fin 14 → Bool) (i : Fin 14) (hi : 2 ≤ i.val) :
    readRegs regs 0 1 none i = regs i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  simp [readRegs, h0, h1]

private theorem ready_updated (regs rf : Fin 8 → Bool)
    (modulus input output sw tw : List Bool) (frame : Fin 6 → List Bool) :
    (SubexpFlatLift.ready rf modulus output [] sw tw frame).stacks =
      Function.update (SubexpFlatLift.ready regs modulus input [] sw tw frame).stacks 8 output := by
  funext i
  simp only [SubexpFlatLift.ready, SubexpFlatLift.state, SubexpFlatLift.stackArray,
    Function.update_apply]
  refine Fin.addCases (m := 14) (n := 6) ?_ ?_ i
  · intro j; fin_cases j <;> simp [Fin.addCases]
  · intro j
    have h8 : Fin.natAdd 14 j ≠ (8 : Fin 20) := by
      intro h; have hv := congrArg Fin.val h; change 14 + j.val = 8 at hv; omega
    simp [Fin.addCases, h8]

theorem quad_eval (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (width : List Bool) (hw : width.length = baseWidth p 1)
    {B : ℕ} (a : Quad (Word B)) (inputWidth : List Bool) (hB : inputWidth.length = B)
    (frame : Fin 6 → List Bool) (d : Data)
    (hstore : ∀ i, d.stacks (quadPorts i) =
      (SubexpFlatLift.ready (d.regs ∘ quadRegs) M.bits (SubexpFlatLift.encode a) []
        inputWidth width frame).stacks i) :
    ∃ n ≤ SubexpOriginQuadProgram.cost B (baseWidth p 1) M.bits.length,
      ∃ rf, (∀ i : Fin 14, 8 ≤ i.val → rf i = d.regs i) ∧
      Eval reduceQuad n d
        ⟨rf, Function.update d.stacks 8
          (SubexpFlatLift.encode (SubexpOriginResidue.quad p M width hw a))⟩ := by
  obtain ⟨smallRegs, n, hn, ht⟩ := SubexpOriginQuadProgram.program_runs p M width hw
    (d.regs ∘ quadRegs) a inputWidth frame hB
  let before := SubexpFlatLift.ready (d.regs ∘ quadRegs) M.bits (SubexpFlatLift.encode a) []
    inputWidth width frame
  let out := SubexpFlatLift.encode (SubexpOriginResidue.quad p M width hw a)
  let after := SubexpFlatLift.ready smallRegs M.bits out [] inputWidth width frame
  let rf := Function.extend quadRegs smallRegs d.regs
  have hin : embedState quadRegs quadPorts d before = d := by
    apply embedState_eq_of_ports _ _ _ _ _ quadRegs.injective quadPorts.injective
    · intros; rfl
    · intros; rfl
    · exact hstore
    · intros; rfl
  have hs : Function.extend quadPorts before.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks hin
  have hout : embedState quadRegs quadPorts d after = ⟨rf, Function.update d.stacks 8 out⟩ := by
    apply congrArg (StructuredProgram.State.mk _)
    rw [show after.stacks = Function.update before.stacks 8 out from
      ready_updated _ _ _ _ _ _ _ _, ProgramLinking.extend_update quadPorts.injective, hs]
    rfl
  refine ⟨n, hn, rf, ?_, ?_⟩
  · intro i hi
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    have hv := congrArg (fun x : Fin 14 => x.val) hj
    change j.val = i.val at hv
    have := j.isLt
    omega
  · have h := eval_call_lifted SubexpOriginQuadProgram.program quadRegs quadPorts d
      quadRegs.injective quadPorts.injective (a := before) (b := after) ht
    simpa only [reduceQuad, hin, hout] using h

def writerResult (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 25 []) 26
      (recordBytes (d.stacks 25).reverse ++ d.stacks 26)⟩

theorem writeRecord_eval (d : Data) :
    Eval writeRecord (5 * (d.stacks 25).length + 7) d (writerResult d) := by
  let small : State 5 6 := ⟨d.regs ∘ writerRegs, d.stacks ∘ writerPorts⟩
  have ht := SubexpArgumentProgram.writer_eval true small (d.stacks 25).reverse
    (by simp [small, writerPorts])
  have hin : embedState writerRegs writerPorts d small = d := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs.injective writerPorts.injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hout : embedState writerRegs writerPorts d
      (SubexpArgumentProgram.afterWriter true small (d.stacks 25).reverse) = writerResult d := by
    apply embedState_eq_of_ports _ _ _ _ _ writerRegs.injective writerPorts.injective
    · intro i; fin_cases i <;> simp [writerResult, small, writerRegs,
        SubexpArgumentProgram.finishedRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [writerRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [writerRegs] using h.symm⟩
      simp [writerResult, h0, h1]
    · intro i; fin_cases i <;> simp [writerResult, small, writerPorts,
        SubexpArgumentProgram.destination, recordBytes]
    · intro i hi
      have h25 : i ≠ 25 := fun h => hi ⟨1, by simpa [writerPorts] using h.symm⟩
      have h26 : i ≠ 26 := fun h => hi ⟨3, by simpa [writerPorts] using h.symm⟩
      simp [writerResult, h25, h26]
  cases ht with
  | call _ ht =>
      have he := eval_call_lifted (SubexpArgumentProgram.writer true) writerRegs writerPorts d
        writerRegs.injective writerPorts.injective ht
      simpa only [writeRecord, hin, hout, List.length_reverse] using he

def finishResult (src dst : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst
      ((d.stacks src).reverse ++ false :: d.stacks dst)⟩

theorem finishList_eval (src dst : Fin 32) (hsd : src ≠ dst) (d : Data) :
    Eval (finishList src dst) (3 * (d.stacks src).length + 8) d (finishResult src dst d) := by
  let d1 : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  let d2 : Data := ⟨d1.regs, Function.update d.stacks src (false :: d.stacks src)⟩
  have h1 : Eval (atom (.set 0 false)) 1 d d1 := .base (.atom _ _)
  have h2 : Eval (atom (.push src 0)) 1 d1 d2 := .base (.atom _ _)
  have h3 := transfer_eval d2 src dst 0 1 hsd (by decide)
  have he : afterTransfer d2 src dst 0 1 = finishResult src dst d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
        simp [afterTransfer, finishResult, d2, d1, readRegs, h0, h1]
    · funext i
      by_cases hs : i = src <;> by_cases ht : i = dst <;>
        simp [afterTransfer, StackRoutines.transferStacks, finishResult, d2, d1,
          hs, ht, hsd, Ne.symm hsd]
  rw [he] at h3
  have hd2len : (d2.stacks src).length = (d.stacks src).length + 1 := by
    simp [d2]
  rw [hd2len] at h3
  have h := h1.seq (h2.seq h3)
  change Eval (finishList src dst) _ d (finishResult src dst d) at h
  convert h using 1
  omega

def extracted (d : Data) (bits : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update (Function.update d.stacks 18 []) 8 bits⟩

theorem extractFirst_eval (d : Data) (bits tail : List Bool)
    (hin : d.stacks 18 = (true :: (Encoding.frame bits ++ tail)).reverse)
    (h19 : d.stacks 19 = []) (h20 : d.stacks 20 = []) (h8 : d.stacks 8 = []) :
    Eval extractFirst
      (3 * (true :: (Encoding.frame bits ++ tail)).length + 9 * bits.length + 2 * tail.length + 14)
      d (extracted d bits) := by
  let d1 := afterTransfer d 18 19 0 1
  have h1 := transfer_eval d 18 19 0 1 (by decide) (by decide)
  have hd1 : d1.stacks 19 = true :: (Encoding.frame bits ++ tail) := by
    simp [d1, afterTransfer, StackRoutines.transferStacks, hin, h19]
  let d2 : Data := ⟨readRegs d1.regs 0 1 (some true),
    Function.update d1.stacks 19 (Encoding.frame bits ++ tail)⟩
  have h2 : Eval (atom (.pop 19 0 1)) 1 d1 d2 := by
    have h := Eval.base (StructuredProgram.Eval.atom (.pop (19 : Fin 32) (0 : Fin 14) 1) d1)
    simpa only [atom, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hd1,
      List.head?_cons, List.tail_cons, d2] using h
  let d3 := RecordPrograms.state degreePorts d2 false true (d2.regs 2) tail bits.reverse
  have hr := RecordPrograms.reader_eval degreePorts d2 bits tail []
    (d2.regs 0) (d2.regs 1) (d2.regs 2)
  have hrin : RecordPrograms.state degreePorts d2 (d2.regs 0) (d2.regs 1) (d2.regs 2)
      (Encoding.frame bits ++ tail) [] = d2 := by
    apply RecordPrograms.state_eq_self <;> try rfl
    simp [d2, d1, degreePorts, afterTransfer, StackRoutines.transferStacks, h20]
  rw [hrin, List.append_nil] at hr
  have h3 : Eval (RecordPrograms.reader degreePorts) (6 * bits.length + 4) d2 d3 := hr
  let d4 := cleared 19 d3
  have hd3_19 : d3.stacks 19 = tail := by
    change d3.stacks degreePorts.source = tail
    exact RecordPrograms.state_source degreePorts d2 false true (d2.regs 2) tail bits.reverse
  have h4 : Eval (clear 19) (2 * tail.length + 3) d3 d4 := by
    rw [← hd3_19]
    exact clear_eval 19 d3
  let d5 := afterTransfer d4 20 8 0 1
  have hd3_20 : d3.stacks 20 = bits.reverse := by
    change d3.stacks degreePorts.payload = bits.reverse
    exact RecordPrograms.state_payload degreePorts d2 false true (d2.regs 2) tail bits.reverse
  have hd4_20 : d4.stacks 20 = bits.reverse := by
    simp [d4, cleared, hd3_20]
  have hd4_20_len : (d4.stacks 20).length = bits.length := by
    rw [hd4_20, List.length_reverse]
  have h5 : Eval (transfer 20 8) (3 * bits.length + 3) d4 d5 := by
    rw [← hd4_20_len]
    exact transfer_eval d4 20 8 0 1 (by decide) (by decide)
  have hs3 : d3.stacks = Function.update (Function.update
      (Function.update d.stacks 18 []) 19 tail) 20 bits.reverse := by
    simp only [d3, d2, d1, RecordPrograms.state, degreePorts, afterTransfer,
      StackRoutines.transferStacks, Function.update_idem]
  have he : d5 = extracted d bits := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0
      · subst i; simp [d5, d4, d3, d2, d1, extracted, afterTransfer, cleared,
          RecordPrograms.state, degreePorts, readRegs]
      by_cases h1 : i = 1
      · subst i; simp [d5, d4, d3, d2, d1, extracted, afterTransfer, cleared,
          RecordPrograms.state, degreePorts, readRegs]
      by_cases h2 : i = 2
      · subst i; simp [d5, d4, d3, d2, d1, extracted, afterTransfer, cleared,
          RecordPrograms.state, degreePorts, readRegs]
      · simp [d5, d4, d3, d2, d1, extracted, afterTransfer, cleared,
          RecordPrograms.state, degreePorts, readRegs, h0, h1, h2]
    · funext i
      simp only [d5, d4, afterTransfer, cleared, StackRoutines.transferStacks,
        hs3, extracted]
      by_cases hi18 : i = 18
      · subst i; simp [h8]
      by_cases hi19 : i = 19
      · subst i; simp [h19, h8]
      by_cases hi20 : i = 20
      · subst i; simp [h20, h8]
      by_cases hi8 : i = 8
      · subst i; simp [h8]
      · simp [hi18, hi19, hi20, hi8]
  rw [he] at h5
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  simpa only [extractFirst, transfer, hin, List.length_reverse,
    show 3 * (true :: (Encoding.frame bits ++ tail)).length + 3 +
      (1 + (6 * bits.length + 4 + (2 * tail.length + 3 + (3 * bits.length + 3)))) =
      3 * (true :: (Encoding.frame bits ++ tail)).length + 9 * bits.length + 2 * tail.length + 14
      by omega] using h

def coordinateCost (B b m : ℕ) (row : Row B) : ℕ :=
  3 * (rowBytes row).length + 2 * (Encoding.encodeList SubexpFlatLift.encode row.2).length +
    36 * B + 56 * b + 33 + SubexpOriginQuadProgram.cost B b m

def coordinateResult (d : Data) (rf : Fin 14 → Bool) (out : List Bool) : Data :=
  ⟨rf, Function.update (Function.update d.stacks 18 []) 21
    ((recordBytes out).reverse ++ d.stacks 21)⟩

private theorem extracted_store (modulus inputWidth width bits : List Bool)
    (d : Data) (hc : clean modulus inputWidth width d) :
    ∀ i, (extracted d bits).stacks (quadPorts i) =
      (SubexpFlatLift.ready ((extracted d bits).regs ∘ quadRegs) modulus bits []
        inputWidth width (fun j => (extracted d bits).stacks
          (quadPorts (Fin.natAdd 14 j)))).stacks i := by
  intro i
  refine Fin.addCases (m := 14) (n := 6) ?_ ?_ i
  · intro j
    have hj := hc.1 j
    fin_cases j <;>
      simp [lowPort, extracted, quadPorts, SubexpFlatLift.ready,
        SubexpFlatLift.state, SubexpFlatLift.stackArray, Fin.addCases] at hj ⊢ <;>
      exact hj
  · intro j
    simp only [SubexpFlatLift.ready, SubexpFlatLift.state,
      SubexpFlatLift.stackArray, Fin.addCases_right]

def packedResult (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update d.stacks 8 [])
      25 []) 26 []) 21 ((recordBytes (d.stacks 8)).reverse ++ d.stacks 21)⟩

private theorem pack_eval (d : Data) (h25 : d.stacks 25 = []) (h26 : d.stacks 26 = []) :
    Eval (.seq (transfer 8 25) (.seq writeRecord (transfer 26 21)))
      (14 * (d.stacks 8).length + 19) d (packedResult d) := by
  let d1 := afterTransfer d 8 25 0 1
  have h1 := transfer_eval d 8 25 0 1 (by decide) (by decide)
  have hs1 : d1.stacks = Function.update (Function.update d.stacks 8 [])
      25 (d.stacks 8).reverse := by
    simp [d1, afterTransfer, StackRoutines.transferStacks, h25]
  have hl1 : (d1.stacks 25).length = (d.stacks 8).length := by rw [hs1]; simp
  let d2 := writerResult d1
  have h2 := writeRecord_eval d1
  have hs2 : d2.stacks = Function.update (Function.update (Function.update d.stacks 8 [])
      25 []) 26 (recordBytes (d.stacks 8)) := by
    simp [d2, writerResult, hs1, h26]
  have hl2 : (d2.stacks 26).length = 2 * (d.stacks 8).length + 2 := by
    rw [hs2]
    simp [recordBytes, Nat.add_assoc]
  let d3 := afterTransfer d2 26 21 0 1
  have h3 := transfer_eval d2 26 21 0 1 (by decide) (by decide)
  have he : d3 = packedResult d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0
      · subst i; simp [d3, d2, d1, afterTransfer, writerResult, packedResult, readRegs]
      by_cases h1 : i = 1
      · subst i; simp [d3, d2, d1, afterTransfer, writerResult, packedResult, readRegs]
      · simp [d3, d2, d1, afterTransfer, writerResult, packedResult, readRegs, h0, h1]
    · funext i
      simp only [d3, afterTransfer, StackRoutines.transferStacks, hs2, packedResult]
      by_cases h8 : i = 8
      · subst i; simp
      by_cases hi25 : i = 25
      · subst i; simp
      by_cases hi26 : i = 26
      · subst i; simp
      by_cases hi21 : i = 21
      · subst i; simp
      · simp [h8, hi25, hi26, hi21]
  have h := h1.seq (h2.seq h3)
  change Eval _ _ d d3 at h
  rw [he] at h
  simpa only [transfer, hl1, hl2,
    show 3 * (d.stacks 8).length + 3 +
      (5 * (d.stacks 8).length + 7 + (3 * (2 * (d.stacks 8).length + 2) + 3)) =
      14 * (d.stacks 8).length + 19 by omega] using h

theorem coordinate_eval (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1)
    (width : List Bool) (hw : width.length = baseWidth p 1)
    {B : ℕ} (row : Row B) (inputWidth : List Bool) (hB : inputWidth.length = B)
    (d : Data) (hc : clean M.bits inputWidth width d)
    (hin : d.stacks 18 = (rowBytes row).reverse) :
    ∃ n ≤ coordinateCost B (baseWidth p 1) M.bits.length row,
      ∃ rf, (∀ i : Fin 14, 8 ≤ i.val → rf i = d.regs i) ∧
      Eval coordinateCallback n d
        (coordinateResult d rf
          (SubexpFlatLift.encode (SubexpOriginResidue.quad p M width hw row.1))) := by
  let bits := SubexpFlatLift.encode row.1
  let tail := Encoding.encodeList SubexpFlatLift.encode row.2
  let out := SubexpFlatLift.encode (SubexpOriginResidue.quad p M width hw row.1)
  have h8 : d.stacks 8 = [] := by simpa [lowPort] using hc.1 8
  have h25 : d.stacks 25 = [] := hc.2.2.2.1
  have h26 : d.stacks 26 = [] := hc.2.2.2.2
  let dE := extracted d bits
  have hE := extractFirst_eval d bits tail hin hc.2.1 hc.2.2.1 h8
  let frame : Fin 6 → List Bool := fun i => dE.stacks (quadPorts (Fin.natAdd 14 i))
  have hstore : ∀ i, dE.stacks (quadPorts i) =
      (SubexpFlatLift.ready (dE.regs ∘ quadRegs) M.bits bits []
        inputWidth width frame).stacks i :=
    extracted_store M.bits inputWidth width bits d hc
  obtain ⟨nQ, hnQ, rQ, hrQ, hQ⟩ := quad_eval p M width hw row.1 inputWidth hB frame dE hstore
  let dQ : Data := ⟨rQ, Function.update dE.stacks 8 out⟩
  have hQ25 : dQ.stacks 25 = [] := by simp [dQ, dE, extracted, h25]
  have hQ26 : dQ.stacks 26 = [] := by simp [dQ, dE, extracted, h26]
  have hP := pack_eval dQ hQ25 hQ26
  have he : packedResult dQ = coordinateResult d (packedResult dQ).regs out := by
    apply state_ext
    · rfl
    · funext i
      by_cases h18 : i = 18
      · subst i; simp [packedResult, dQ, dE, extracted, coordinateResult]
      by_cases hi8 : i = 8
      · subst i; simp [packedResult, dQ, dE, extracted, coordinateResult, h8]
      by_cases hi25 : i = 25
      · subst i; simp [packedResult, dQ, dE, extracted, coordinateResult, h25]
      by_cases hi26 : i = 26
      · subst i; simp [packedResult, dQ, dE, extracted, coordinateResult, h26]
      by_cases hi21 : i = 21
      · subst i; simp [packedResult, dQ, dE, extracted, coordinateResult]
      · simp [packedResult, dQ, dE, extracted, coordinateResult,
          h18, hi8, hi25, hi26, hi21]
  have hregs : ∀ i : Fin 14, 8 ≤ i.val → (packedResult dQ).regs i = d.regs i := by
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    have hqi := hrQ i hi
    simpa [packedResult, dQ, dE, extracted,
      readRegs, h0, h1] using hqi
  have h := hE.seq (hQ.seq hP)
  rw [he] at h
  refine ⟨_, ?_, (packedResult dQ).regs, hregs, h⟩
  have hbits : bits.length = 4 * B := SubexpFlatLift.encode_length row.1
  have hout : (dQ.stacks 8).length = 4 * baseWidth p 1 := by simp [dQ, out]
  change 3 * (true :: (Encoding.frame bits ++ tail)).length + 9 * bits.length +
    2 * tail.length + 14 + (nQ + (14 * (dQ.stacks 8).length + 19)) ≤
    3 * (true :: (Encoding.frame bits ++ tail)).length + 2 * tail.length +
      36 * B + 56 * baseWidth p 1 + 33 +
        SubexpOriginQuadProgram.cost B (baseWidth p 1) M.bits.length
  omega

end SubexponentialSAT.SubexpOriginCalls

end OAI.Algorithms
