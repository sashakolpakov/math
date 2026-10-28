import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseOperands
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProduct

namespace OAI.Algorithms

/-!
# Physical dense multiplication service

The actual pair-generation/projection core is enclosed by the same operand
parser, slot copier, result framer, and register reset used for addition.
The context contract describes stored words and empty workspace only. The
execution and exact output are supplied by the concrete core theorem.
-/

namespace SubexponentialSAT.SubexpDenseMultiplication

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpDenseOperandWrappers SubexpDenseOperands
open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpCanonicalWords SubexpDenseSerialization
open SubexpQuarticFlatLift SubexpQuarticFlatMul

abbrev Data := SubexpDenseOperandWrappers.Data

/-- The multiplication bank, reduction word, key width and parser scratch.
The lower workspace is the same concrete contract as LOAD and ADD. -/
structure Ready (d : Data) (modulus width master reduction keyWidth : List Bool) : Prop where
  core : CoreReady d modulus width master
  bank : ∀ i : Fin 128, 30 ≤ i.val → i.val < 91 → d.stacks i = []
  reduction : d.stacks 91 = reduction
  keyWidth : d.stacks 92 = keyWidth
  scratch : ∀ i : Fin 128, 93 ≤ i.val → i.val < 100 → d.stacks i = []

def ContextReady (context : Fin 124 → List Bool)
    (modulus width master reduction keyWidth : List Bool) : Prop :=
  Ready (physicalState false false false [] [] [] context)
    modulus width master reduction keyWidth

theorem physicalState_frame (v pr op : Bool) (code depth operands : List Bool)
    (context : Fin 124 → List Bool) (i : Fin 128)
    (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    (physicalState v pr op code depth operands context).stacks i =
      (physicalState false false false [] [] [] context).stacks i := by
  obtain ⟨j, rfl⟩ := SubexpPostfixGlobal.ports.surjective i
  revert h26 h27 h28 h29
  refine Fin.addCases (m := 4) (n := 124) (fun j => ?_) (fun j => ?_) j
  · fin_cases j <;> simp
  · intro _ _ _ _
    simp only [physicalState, StructuredProgram.State.ofCfg,
      SubexpPostfixGlobal.physicalCfg_context]

theorem physicalState_high (v pr op : Bool) (code depth operands : List Bool)
    (context : Fin 124 → List Bool) (i : Fin 128) (hi : 30 ≤ i.val) :
    (physicalState v pr op code depth operands context).stacks i =
      (physicalState false false false [] [] [] context).stacks i := by
  apply physicalState_frame
  all_goals intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi

theorem ContextReady.physical {context : Fin 124 → List Bool}
    {modulus width master reduction keyWidth : List Bool}
    (h : ContextReady context modulus width master reduction keyWidth)
    (v pr op : Bool) (code depth operands : List Bool) :
    Ready (physicalState v pr op code depth operands context)
      modulus width master reduction keyWidth := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (show SubexpDenseOperands.ContextReady context modulus width master from h.core).physical
      v pr op code depth operands
  · intro i hlo hhi
    rw [physicalState_high _ _ _ _ _ _ _ i hlo]
    exact h.bank i hlo hhi
  · rw [physicalState_high _ _ _ _ _ _ _ 91 (by decide)]
    exact h.reduction
  · rw [physicalState_high _ _ _ _ _ _ _ 92 (by decide)]
    exact h.keyWidth
  · intro i hlo hhi
    rw [physicalState_high _ _ _ _ _ _ _ i (by omega)]
    exact h.scratch i hlo hhi

theorem Ready.workspace {d : Data} {modulus width master keyWidth : List Bool}
    {B : ℕ} {t : Quad (Word B)}
    (h : Ready d modulus width master (flat t) keyWidth) :
    ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace modulus width t i := by
  intro i
  by_cases hi : i.val < 61
  · simpa only [densePorts, Function.Embedding.coeFn_mk, densePort, dite_eq_left hi,
      SubexpQuarticDenseCall.workspace, bankStore] using
      h.bank ⟨i.val + 30, by omega⟩
        (by change 30 ≤ i.val + 30; omega)
        (by change i.val + 30 < 91; omega)
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 16, i = Fin.natAdd 61 j := by
      refine ⟨⟨i.val - 61, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    fin_cases j
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 0
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 1
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 2
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 3
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 4
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 5
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 6
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 7
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 8
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 11
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 12
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 13
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        Fin.addCases, Fin.coe_ofNat_eq_mod] using h.reduction
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 10
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 14
    · simpa [densePorts, densePort, SubexpQuarticDenseCall.workspace, bankStore,
        coreStacks, readyStacks, Fin.addCases, Fin.coe_ofNat_eq_mod] using h.core 15

theorem addPrepared_high (d : Data) (left right tail : List Bool)
    (i : Fin 128) (hi : 30 ≤ i.val) :
    (addPrepared d left right tail).stacks i = d.stacks i := by
  have hn (k : Fin 128) (hk : k.val < 30) : i ≠ k := by
    intro he
    subst k
    omega
  simp only [addPrepared_stacks,
    Function.update_of_ne (hn 21 (by decide)),
    Function.update_of_ne (hn 20 (by decide)),
    Function.update_of_ne (hn 29 (by decide)),
    Function.update_of_ne (hn 22 (by decide)),
    Function.update_of_ne (hn 23 (by decide)),
    Function.update_of_ne (hn 27 (by decide))]

theorem addPrepared_workspace (d : Data) (left right tail modulus width : List Bool)
    {B : ℕ} (t : Quad (Word B))
    (h : ∀ i, d.stacks (densePorts i) = SubexpQuarticDenseCall.workspace modulus width t i) :
    ∀ i, (addPrepared d left right tail).stacks (densePorts i) =
      SubexpQuarticDenseCall.workspace modulus width t i := by
  intro i
  simpa only [addPrepared_stacks,
    Function.update_of_ne (SubexpDenseProgram.Product.mulPort_ne i 21 (by decide)),
    Function.update_of_ne (SubexpDenseProgram.Product.mulPort_ne i 20 (by decide)),
    Function.update_of_ne (SubexpDenseProgram.Product.mulPort_ne i 29 (by decide)),
    Function.update_of_ne (SubexpDenseProgram.Product.mulPort_ne i 22 (by decide)),
    Function.update_of_ne (SubexpDenseProgram.Product.mulPort_ne i 23 (by decide)),
    Function.update_of_ne (SubexpDenseProgram.Product.mulPort_ne i 27 (by decide))] using h i

theorem addPrepared_projection (d : Data) (left right tail modulus width master : List Bool)
    (h : CoreReady d modulus width master) (h99 : d.stacks 99 = []) :
    SubexpDenseProgram.Product.localProjectionState (addPrepared d left right tail) =
      SubexpDenseProgram.Projection.controllerState
        ((addPrepared d left right tail).regs ∘ SubexpDenseProgram.Product.lowEight)
        modulus [] width [] [] master [false] [] right master := by
  have hp := addPrepared_local d left right tail modulus width master h
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    by_cases hi : i = 22
    · subst i
      change (addPrepared d left right tail).stacks 99 = []
      simpa only [addPrepared_high d left right tail 99 (by decide)] using h99
    · have hport : SubexpDenseProgram.Product.projectionPorts i = coreStacks i := by
        simp only [SubexpDenseProgram.Product.projectionPorts, ite_eq_right hi]
        apply Fin.ext
        rfl
      change (addPrepared d left right tail).stacks
        (SubexpDenseProgram.Product.projectionPorts i) = _
      rw [hport]
      change (localState (addPrepared d left right tail)).stacks i = _
      rw [hp, SubexpDenseProgram.Product.controller_input_update]
      simp only [Function.update_of_ne hi, localState, coreRegs,
        SubexpDenseProgram.Product.lowEight]

def service := binaryProgram SubexpDenseProgram.Product.mulCoreProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D+1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))

def bound (P Q : CoeffList D (QuarticCode p D)) : ℕ :=
  SubexpDenseProgram.Product.multiplicationTime p D M t P Q slots +
    11 * ((encodeFixedQuarticCoefficients p D P).length +
      (encodeFixedQuarticCoefficients p D Q).length) +
    7 * (SubexpDenseProgram.Projection.queryBytes slots).length +
    8 * (encodeFixedQuarticCoefficients p D
      (programMul (preparedProgram p D M t z o) slots P Q).1).length + 57

theorem core_runsIn (c : Fin 4 → ZMod (p^(D+1)))
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (d : Data) (tail width : List Bool) (hwidth : width.length = baseWidth p (D+1))
    (h : Ready d M.bits width (SubexpDenseProgram.Projection.queryBytes slots)
      (flat t) (List.replicate (indexBits D) true)) :
    ∃ regs, RunsIn SubexpDenseProgram.Product.mulCoreProgram
      (SubexpDenseProgram.Product.multiplicationTime p D M t P Q slots)
      ((addPrepared d (encodeFixedQuarticCoefficients p D P)
        (encodeFixedQuarticCoefficients p D Q) tail).withPC
        (some SubexpDenseProgram.Product.mulCoreProgram.entry))
      ((physicalCoreOutput (addPrepared d (encodeFixedQuarticCoefficients p D P)
        (encodeFixedQuarticCoefficients p D Q) tail) regs
        (encodeFixedQuarticCoefficients p D
          (programMul (preparedProgram p D M t z o) slots P Q).1)).withPC none) := by
  let left := encodeFixedQuarticCoefficients p D P
  let right := encodeFixedQuarticCoefficients p D Q
  let input := addPrepared d left right tail
  have h22 : d.stacks 22 = [] := h.core.empty 22 (by decide) (by decide) (by decide)
  have h23 : d.stacks 23 = [] := h.core.empty 23 (by decide) (by decide) (by decide)
  have hlo (i : Fin 26) (hi : i ≠ 5 ∧ i ≠ 10 ∧ i ≠ 25) :
      d.stacks (coreStacks i) = [] := h.core.empty i hi.1 hi.2.1 hi.2.2
  have hhi (i : Fin 128) (ha : 93 ≤ i.val) (hb : i.val < 100) :
      input.stacks i = [] := by
    rw [show input = addPrepared d left right tail from rfl,
      addPrepared_high _ _ _ _ _ (by omega)]
    exact h.scratch i ha hb
  obtain ⟨n, e, hn, heval, hs⟩ := SubexpDenseProgram.Product.mulCore_eval
    p D M c t z o hz hcanonical P Q slots hP hQ input width hwidth
    (addPrepared_workspace d left right tail M.bits width t h.workspace)
    (by simp [input, addPrepared_stacks, left, h22])
    (by simp [input, addPrepared_stacks, right, h23])
    (by simpa only [input, addPrepared_high d left right tail 92 (by decide)] using h.keyWidth)
    (addPrepared_projection d left right tail M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) h.core (h.scratch 99 (by decide) (by decide)))
    (by simpa [input, addPrepared_stacks, coreStacks] using hlo 16 (by decide))
    (by simpa [input, addPrepared_stacks, coreStacks] using hlo 17 (by decide))
    (by simpa [input, addPrepared_stacks, coreStacks] using hlo 18 (by decide))
    (by simpa [input, addPrepared_stacks, coreStacks] using hlo 19 (by decide))
    (by simpa [input, addPrepared_stacks, coreStacks] using hlo 24 (by decide))
    (hhi 93 (by decide) (by decide)) (hhi 94 (by decide) (by decide))
    (hhi 95 (by decide) (by decide)) (hhi 96 (by decide) (by decide))
    (hhi 97 (by decide) (by decide)) (hhi 98 (by decide) (by decide))
    (hhi 99 (by decide) (by decide))
  have he : e = physicalCoreOutput input e.regs
      (encodeFixedQuarticCoefficients p D
        (programMul (preparedProgram p D M t z o) slots P Q).1) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  have ht := StructuredCalls.compiled_halt_trace heval 22 21
  rw [he] at ht
  exact ⟨e.regs, n+1, hn, ht⟩

/-- Actual multiplication on every pair of retained coefficient lists. The
finite service program is independent of p, D, slots and the operands. -/
theorem implements (c : Fin 4 → ZMod (p^(D+1)))
    (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
    (hcanonical : CanonicalQuad p (D+1) z)
    (width : List Bool) (hwidth : width.length = baseWidth p (D+1))
    (context : Fin 124 → List Bool)
    (hcontext : ContextReady context M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (flat t)
      (List.replicate (indexBits D) true)) :
    SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList
      (encodeFixedQuarticCoefficients p D)
      (fun P Q => (programMul (preparedProgram p D M t z o) slots P Q).1)
      true service (bound p D M t z o slots) context := by
  intro P Q hP hQ xs code depth
  let left := encodeFixedQuarticCoefficients p D P
  let right := encodeFixedQuarticCoefficients p D Q
  let bits := encodeFixedQuarticCoefficients p D
    (programMul (preparedProgram p D M t z o) slots P Q).1
  let tail := Encoding.encodeList (encodeFixedQuarticCoefficients p D) xs
  let d := physicalState true true true code depth
    (true :: (Encoding.frame right ++ true :: (Encoding.frame left ++ tail))) context
  have hr : Ready d M.bits width (SubexpDenseProgram.Projection.queryBytes slots)
      (flat t) (List.replicate (indexBits D) true) :=
    hcontext.physical true true true code depth _
  have hc := core_runsIn p D M t z o slots c hz hcanonical P Q hP hQ d tail width hwidth hr
  have hout := binary_runsIn SubexpDenseProgram.Product.mulCoreProgram d left right bits tail
    (by simp [d, physicalState, StructuredProgram.State.ofCfg])
    (hr.core.empty 20 (by decide) (by decide) (by decide))
    (hr.core.empty 21 (by decide) (by decide) (by decide))
    (hr.core.empty 22 (by decide) (by decide) (by decide))
    (hr.core.empty 23 (by decide) (by decide) (by decide))
    (hr.core.empty 24 (by decide) (by decide) (by decide))
    (by simp [d, physicalState, StructuredProgram.State.ofCfg]) hc
  rw [hr.core.master] at hout
  simpa only [service, bound, d, left, right, bits, tail, Encoding.encodeList,
    physicalState_withPC, result_physical] using hout

/-- Fixed polynomial overhead, including operand and result framing, around
the core's fixed polynomial. The five arguments are numeric widths and list
lengths; no polynomial degree depends on them. -/
def envelope (B I leftCount rightCount slotCount : ℕ) : ℕ :=
  SubexpDenseProgram.Product.denseEnvelope B I leftCount rightCount slotCount +
    11 * ((1 + SubexpDenseProgram.Product.recordBits B I * leftCount) +
      (1 + SubexpDenseProgram.Product.recordBits B I * rightCount)) +
    7 * (1 + (2 * I + 2) * slotCount) +
    8 * (1 + SubexpDenseProgram.Product.recordBits B I * slotCount) + 57

theorem bound_le_envelope (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (hslots : ∀ a ∈ slots, Retained D a) :
    bound p D M t z o slots P Q ≤
      envelope (baseWidth p (D+1)) (indexBits D) P.length Q.length slots.length := by
  have hc := SubexpDenseProgram.Product.multiplicationTime_le_envelope
    p D M t P Q slots hP hQ hslots
  have hl := SubexpDenseProgram.Product.retained_serialized_length_le p D P hP
  have hr := SubexpDenseProgram.Product.retained_serialized_length_le p D Q hQ
  have hquery : ∀ q ∈ (slots.map fixedKey).reverse, (id q).length ≤ indexBits D := by
    intro q hq
    have hm : q ∈ slots.map fixedKey := by simpa only [List.mem_reverse] using hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact (fixedKey_length a (hslots a ha)).le
  have hmaster : (SubexpDenseProgram.Projection.queryBytes slots).length ≤
      1 + (2 * indexBits D + 2) * slots.length := by
    simpa only [SubexpDenseProgram.Projection.queryBytes, List.length_reverse,
      List.length_map] using Encoding.length_encodeList_upper id
        (slots.map fixedKey).reverse (indexBits D) hquery
  let ops := preparedProgram p D M t z o
  have hvalid : SubexpProjectedEvaluation.RetainedList (programMul ops slots P Q).1 :=
    SubexpProjectedEvaluation.programProject_retained ops slots hslots (programRawMul ops P Q).1
  have hout := SubexpDenseProgram.Product.retained_serialized_length_le p D
    (programMul ops slots P Q).1 hvalid
  have hlength : (programMul ops slots P Q).1.length = slots.length := by
    have hk := congrArg List.length (SubexpProjectedEvaluation.programProject_keys
      ops slots (programRawMul ops P Q).1)
    simpa only [List.length_map, programMul] using hk
  rw [hlength] at hout
  change (encodeFixedQuarticCoefficients p D
    (programMul (preparedProgram p D M t z o) slots P Q).1).length ≤ _ at hout
  unfold bound envelope
  omega

end SubexponentialSAT.SubexpDenseMultiplication

end OAI.Algorithms
