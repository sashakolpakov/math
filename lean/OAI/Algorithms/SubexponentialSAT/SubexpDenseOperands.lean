import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandWrappers
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProjection
import OAI.Algorithms.SubexponentialSAT.SubexpProjectedEvaluation

namespace OAI.Algorithms

/-!
# Concrete dense LOAD and ADD services on the shared interpreter machine

The only context requirements are the actual modulus, unary scalar width,
serialized slot master, and empty local scratch ports. All other caller
stacks are preserved. No arithmetic execution or output-equality premise
appears in the final interpreter contracts.
-/

namespace SubexponentialSAT.SubexpDenseOperands

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpDenseOperandWrappers SubexpDenseOperandIO
open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpCanonicalWords SubexpDenseSerialization
open SubexpPostfixGlobal (physicalCfg)

theorem load_runsIn {l B : ℕ} (core : Program 8 26 l) (d : SubexpDenseOperandWrappers.Data)
    (raw bits tail : List Bool)
    (hin : d.stacks 27 = true :: (Encoding.frame raw ++ tail))
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h24 : d.stacks 24 = []) (h29 : d.stacks 29 = [])
    (hcore : ∃ regs, RunsIn core B
      ((localState (loadPrepared d raw tail)).withPC (some core.entry))
      ((localOutput (loadPrepared d raw tail) regs bits).withPC none)) :
    RunsIn (loadProgram core)
      (B + 11 * raw.length + 7 * (d.stacks 25).length + 8 * bits.length + 46)
      (d.withPC (some (loadProgram core).entry)) ((result d bits tail).withPC none) := by
  obtain ⟨regs, n, hn, ht⟩ := hcore
  have h := StructuredCalls.compiled_halt_trace
    (load_eval core d raw bits tail regs hin h20 h21 h22 h24 h29 ht) 27 27
  refine ⟨n + 11 * raw.length + 7 * (d.stacks 25).length + 8 * bits.length + 46,
    by omega, ?_⟩
  simpa only [loadProgram, Nat.add_assoc] using h

theorem add_runsIn {l B : ℕ} (core : Program 8 26 l) (d : SubexpDenseOperandWrappers.Data)
    (left right bits tail : List Bool)
    (hin : d.stacks 27 = true :: (Encoding.frame right ++
      true :: (Encoding.frame left ++ tail)))
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) (h29 : d.stacks 29 = [])
    (hcore : ∃ regs, RunsIn core B
      ((localState (addPrepared d left right tail)).withPC (some core.entry))
      ((localOutput (addPrepared d left right tail) regs bits).withPC none)) :
    RunsIn (addProgram core)
      (B + 11 * (left.length + right.length) + 7 * (d.stacks 25).length +
        8 * bits.length + 57)
      (d.withPC (some (addProgram core).entry)) ((result d bits tail).withPC none) := by
  obtain ⟨regs, n, hn, ht⟩ := hcore
  have h := StructuredCalls.compiled_halt_trace
    (add_eval core d left right bits tail regs hin h20 h21 h22 h23 h24 h29 ht) 27 27
  refine ⟨n + 11 * (left.length + right.length) + 7 * (d.stacks 25).length +
    8 * bits.length + 57, by omega, ?_⟩
  simpa only [addProgram, Nat.add_assoc] using h

theorem binary_runsIn {l B : ℕ} (core : Program 16 128 l)
    (d : SubexpDenseOperandWrappers.Data) (left right bits tail : List Bool)
    (hin : d.stacks 27 = true :: (Encoding.frame right ++
      true :: (Encoding.frame left ++ tail)))
    (h20 : d.stacks 20 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) (h29 : d.stacks 29 = [])
    (hcore : ∃ regs, RunsIn core B
      ((addPrepared d left right tail).withPC (some core.entry))
      ((physicalCoreOutput (addPrepared d left right tail) regs bits).withPC none)) :
    RunsIn (binaryProgram core)
      (B + 11 * (left.length + right.length) + 7 * (d.stacks 25).length +
        8 * bits.length + 57)
      (d.withPC (some (binaryProgram core).entry)) ((result d bits tail).withPC none) := by
  obtain ⟨regs, n, hn, ht⟩ := hcore
  have h := StructuredCalls.compiled_halt_trace
    (binary_eval core d left right bits tail regs hin h20 h21 h22 h23 h24 h29 ht) 27 27
  refine ⟨n + 11 * (left.length + right.length) + 7 * (d.stacks 25).length +
    8 * bits.length + 57, by omega, ?_⟩
  simpa only [binaryProgram, Nat.add_assoc] using h

def readyStacks (modulus width master : List Bool) (i : Fin 26) : List Bool :=
  if i = 5 then modulus else if i = 10 then width else if i = 25 then master else []

def CoreReady (d : SubexpDenseOperandWrappers.Data) (modulus width master : List Bool) : Prop :=
  ∀ i : Fin 26, d.stacks (coreStacks i) = readyStacks modulus width master i

theorem CoreReady.empty {d : SubexpDenseOperandWrappers.Data} {modulus width master : List Bool}
    (h : CoreReady d modulus width master) (i : Fin 26)
    (h5 : i ≠ 5) (h10 : i ≠ 10) (h25 : i ≠ 25) :
    d.stacks (coreStacks i) = [] := by
  simpa only [readyStacks, ite_eq_right h5, ite_eq_right h10, ite_eq_right h25] using h i

theorem CoreReady.master {d : SubexpDenseOperandWrappers.Data} {modulus width master : List Bool}
    (h : CoreReady d modulus width master) : d.stacks 25 = master := by
  simpa [coreStacks, readyStacks] using h 25

theorem loadPrepared_local (d : SubexpDenseOperandWrappers.Data)
    (raw tail modulus width master : List Bool) (h : CoreReady d modulus width master) :
    localState (loadPrepared d raw tail) =
      SubexpDenseProgram.Projection.controllerState (localState (loadPrepared d raw tail)).regs
        modulus [] width [] [] master [false] raw [] master := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · have h20 := h.empty 20 (by decide) (by decide) (by decide)
    have h21 := h.empty 21 (by decide) (by decide) (by decide)
    have h22 := h.empty 22 (by decide) (by decide) (by decide)
    have h25 := h.master
    funext i
    have hi := h i
    simp only [localState, Function.comp_apply, loadPrepared_stacks]
    fin_cases i <;>
      simp_all [coreStacks, readyStacks, SubexpDenseProgram.Projection.controllerState, SubexpDenseProgram.Projection.extendState,
        SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
        SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod]

theorem addPrepared_local (d : SubexpDenseOperandWrappers.Data)
    (left right tail modulus width master : List Bool) (h : CoreReady d modulus width master) :
    localState (addPrepared d left right tail) =
      SubexpDenseProgram.Projection.controllerState (localState (addPrepared d left right tail)).regs
        modulus [] width [] [] master [false] left right master := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · have h20 := h.empty 20 (by decide) (by decide) (by decide)
    have h21 := h.empty 21 (by decide) (by decide) (by decide)
    have h22 := h.empty 22 (by decide) (by decide) (by decide)
    have h23 := h.empty 23 (by decide) (by decide) (by decide)
    have h25 := h.master
    funext i
    have hi := h i
    simp only [localState, Function.comp_apply, addPrepared_stacks]
    fin_cases i <;>
      simp_all [coreStacks, readyStacks, SubexpDenseProgram.Projection.controllerState, SubexpDenseProgram.Projection.extendState,
        SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
        SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod]

theorem localOutput_of_controller (d : SubexpDenseOperandWrappers.Data)
    (before after : Fin 8 → Bool) (modulus width queries left right master bits : List Bool)
    (h : localState d = SubexpDenseProgram.Projection.controllerState before modulus [] width [] [] queries [false]
      left right master) :
    localOutput d after bits =
      SubexpDenseProgram.Projection.controllerState after modulus [] width [] [] [] bits left right master := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · change Function.update (Function.update (localState d).stacks 20 []) 21 bits = _
    rw [h]
    funext i
    fin_cases i <;> rfl

def physicalState (v pr op : Bool) (code depth operands : List Bool)
    (context : Fin 124 → List Bool) : SubexpDenseOperandWrappers.Data :=
  StructuredProgram.State.ofCfg (physicalCfg (l := 1) none v pr op code depth operands context)

theorem physicalState_withPC {l : ℕ} (pc : Option (Fin l)) (v pr op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalState v pr op code depth operands context).withPC pc =
      physicalCfg pc v pr op code depth operands context := rfl

theorem physicalState_low (v pr op : Bool) (code depth operands : List Bool)
    (context : Fin 124 → List Bool) (i : Fin 26) :
    (physicalState v pr op code depth operands context).stacks (coreStacks i) =
      (physicalState false false false [] [] [] context).stacks (coreStacks i) := by
  fin_cases i <;> rfl

/-- Concrete metadata and empty local work ports; all other context is arbitrary. -/
def ContextReady (context : Fin 124 → List Bool) (modulus width master : List Bool) : Prop :=
  CoreReady (physicalState false false false [] [] [] context) modulus width master

theorem ContextReady.physical {context : Fin 124 → List Bool} {modulus width master : List Bool}
    (h : ContextReady context modulus width master) (v pr op : Bool)
    (code depth operands : List Bool) :
    CoreReady (physicalState v pr op code depth operands context) modulus width master := by
  intro i
  rw [physicalState_low]
  exact h i

private theorem cfg_ext {l : ℕ} {a b : Cfg 16 128 l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

theorem result_physical {l : ℕ} (pc : Option (Fin l)) (v pr op : Bool)
    (code depth operands bits tail : List Bool) (context : Fin 124 → List Bool) :
    (result (physicalState v pr op code depth operands context) bits tail).withPC pc =
      physicalCfg pc false false false code depth
        (true :: (Encoding.frame bits ++ tail)) context := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    obtain ⟨j, rfl⟩ := SubexpPostfixGlobal.ports.surjective i
    refine Fin.addCases (m := 4) (n := 124) ?_ ?_ j
    · intro k
      fin_cases k <;>
        simp [result, physicalState, StructuredProgram.State.ofCfg]
    · intro k
      have hn : SubexpPostfixGlobal.ports (Fin.natAdd 4 k) ≠ (27 : Fin 128) := by
        intro h
        have he := SubexpPostfixGlobal.ports.injective
          (h.trans SubexpPostfixGlobal.ports_two.symm)
        have hv := congrArg Fin.val he
        dsimp at hv
        omega
      simp [result, physicalState, StructuredProgram.State.ofCfg, hn]

def loadService := loadProgram SubexpDenseProgram.Projection.projectProgram
def addService := addProgram SubexpDenseProgram.Projection.addProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D+1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))

def loadBound (P₀ : CoeffList D (QuarticCode p D)) : ℕ :=
  SubexpDenseProgram.Projection.projectionTime p D M P₀ slots +
    11 * (encodeFixedQuarticCoefficients p D P₀).length +
    7 * (SubexpDenseProgram.Projection.queryBytes slots).length +
    8 * (encodeFixedQuarticCoefficients p D
      (programProject (preparedProgram p D M t z o) slots P₀).1).length + 46

def addBound (P₀ Q : CoeffList D (QuarticCode p D)) : ℕ :=
  SubexpDenseProgram.Projection.additionTime p D M P₀ Q slots +
    11 * ((encodeFixedQuarticCoefficients p D P₀).length +
      (encodeFixedQuarticCoefficients p D Q).length) +
    7 * (SubexpDenseProgram.Projection.queryBytes slots).length +
    8 * (encodeFixedQuarticCoefficients p D
      (programAdd (preparedProgram p D M t z o) slots P₀ Q).1).length + 57

variable (c : Fin 4 → ZMod (p^(D+1)))
  (hz : quotientDenote c (z.map (wordValue p (D+1))) = 0)
  (hcanonical : CanonicalQuad p (D+1) z)
  (width : List Bool) (hwidth : width.length = baseWidth p (D+1))
  (context : Fin 124 → List Bool)
  (hcontext : ContextReady context M.bits width (SubexpDenseProgram.Projection.queryBytes slots))

include hz hcanonical hwidth hcontext

/-- LOAD accepts every raw coefficient list, including non-retained keys and
duplicate terms. Its core execution is discharged by the concrete projection. -/
theorem load_implements :
    SubexpProjectedEvaluation.LoadImplementsGlobal
      (encodeFixedQuarticCoefficients p D)
      (fun P₀ => (programProject (preparedProgram p D M t z o) slots P₀).1)
      loadService (loadBound p D M t z o slots) context := by
  intro P₀ xs code depth op
  let raw := encodeFixedQuarticCoefficients p D P₀
  let bits := encodeFixedQuarticCoefficients p D
    (programProject (preparedProgram p D M t z o) slots P₀).1
  let tail := Encoding.encodeList (encodeFixedQuarticCoefficients p D) xs
  let d := physicalState true false op code depth (true :: (Encoding.frame raw ++ tail)) context
  have hr : CoreReady d M.bits width (SubexpDenseProgram.Projection.queryBytes slots) :=
    hcontext.physical true false op code depth _
  have hp := loadPrepared_local d raw tail M.bits width (SubexpDenseProgram.Projection.queryBytes slots) hr
  obtain ⟨regs, n, hn, ht⟩ := SubexpDenseProgram.Projection.projectProgram_exact p D M c t z o hz hcanonical
    P₀ slots width [] hwidth (localState (loadPrepared d raw tail)).regs
  have hc : ∃ regs, RunsIn SubexpDenseProgram.Projection.projectProgram (SubexpDenseProgram.Projection.projectionTime p D M P₀ slots)
      ((localState (loadPrepared d raw tail)).withPC (some SubexpDenseProgram.Projection.projectProgram.entry))
      ((localOutput (loadPrepared d raw tail) regs bits).withPC none) := by
    refine ⟨SubexpCoefficientLookup.normalized regs false true false, n, hn, ?_⟩
    rw [localOutput_of_controller _ _ _ _ _ _ _ _ _ _ hp, hp]
    exact ht
  have h := load_runsIn SubexpDenseProgram.Projection.projectProgram d raw bits tail
    (by simp [d, physicalState, StructuredProgram.State.ofCfg])
    (hr.empty 20 (by decide) (by decide) (by decide))
    (hr.empty 21 (by decide) (by decide) (by decide))
    (hr.empty 22 (by decide) (by decide) (by decide))
    (hr.empty 24 (by decide) (by decide) (by decide))
    (by simp [d, physicalState, StructuredProgram.State.ofCfg]) hc
  rw [hr.master] at h
  simpa only [loadService, loadBound, d, raw, bits, tail, Encoding.encodeList,
    physicalState_withPC, result_physical] using h

/-- ADD calls the concrete two-list scanner. The retained-input interface is
the one consumed by the projected interpreter; the scanner also handles raw keys. -/
theorem add_implements :
    SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList
      (encodeFixedQuarticCoefficients p D)
      (fun P₀ Q => (programAdd (preparedProgram p D M t z o) slots P₀ Q).1)
      false addService (addBound p D M t z o slots) context := by
  intro P₀ Q _ _ xs code depth
  let left := encodeFixedQuarticCoefficients p D P₀
  let right := encodeFixedQuarticCoefficients p D Q
  let bits := encodeFixedQuarticCoefficients p D
    (programAdd (preparedProgram p D M t z o) slots P₀ Q).1
  let tail := Encoding.encodeList (encodeFixedQuarticCoefficients p D) xs
  let d := physicalState true true false code depth
    (true :: (Encoding.frame right ++ true :: (Encoding.frame left ++ tail))) context
  have hr : CoreReady d M.bits width (SubexpDenseProgram.Projection.queryBytes slots) :=
    hcontext.physical true true false code depth _
  have hp := addPrepared_local d left right tail M.bits width (SubexpDenseProgram.Projection.queryBytes slots) hr
  obtain ⟨regs, n, hn, ht⟩ := SubexpDenseProgram.Projection.addProgram_exact p D M c t z o hz hcanonical
    P₀ Q slots width hwidth (localState (addPrepared d left right tail)).regs
  have hc : ∃ regs, RunsIn SubexpDenseProgram.Projection.addProgram (SubexpDenseProgram.Projection.additionTime p D M P₀ Q slots)
      ((localState (addPrepared d left right tail)).withPC (some SubexpDenseProgram.Projection.addProgram.entry))
      ((localOutput (addPrepared d left right tail) regs bits).withPC none) := by
    refine ⟨SubexpCoefficientLookup.normalized regs false true false, n, hn, ?_⟩
    rw [localOutput_of_controller _ _ _ _ _ _ _ _ _ _ hp, hp]
    exact ht
  have h := add_runsIn SubexpDenseProgram.Projection.addProgram d left right bits tail
    (by simp [d, physicalState, StructuredProgram.State.ofCfg])
    (hr.empty 20 (by decide) (by decide) (by decide))
    (hr.empty 21 (by decide) (by decide) (by decide))
    (hr.empty 22 (by decide) (by decide) (by decide))
    (hr.empty 23 (by decide) (by decide) (by decide))
    (hr.empty 24 (by decide) (by decide) (by decide))
    (by simp [d, physicalState, StructuredProgram.State.ofCfg]) hc
  rw [hr.master] at h
  simpa only [addService, addBound, d, left, right, bits, tail, Encoding.encodeList,
    physicalState_withPC, result_physical] using h

end SubexponentialSAT.SubexpDenseOperands

end OAI.Algorithms
