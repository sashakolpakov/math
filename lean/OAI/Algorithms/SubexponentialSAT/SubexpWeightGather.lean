import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentGather
import OAI.Algorithms.SubexponentialSAT.SubexpWeightEmit
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ModularPrograms

namespace OAI.Algorithms

/-! The support-driven weight input producer. Indices are framed unary words,
matching `GatherProgram.indexRecords`. The exponent master and coordinate
master are retained while each selected pair is serialized. -/

namespace SubexponentialSAT.SubexpWeightGather

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 8 24

def state (regs : Fin 8 → Bool) (exponents coordinates width target source output payload : List Bool) : Data :=
  ⟨regs,![exponents,[],[],[],[],[],[],coordinates,[],[],width,[],[],[],[],[],output,[],[],source,payload,target,[],[]]⟩

def ports : RecordPrograms.Ports 8 24 where
  tag := 0
  present := 1
  found := 7
  source := 19
  payload := 20
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def exponentRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def exponentPorts : Fin 7 → Fin 24 := Fin.castAdd 17
def coordinatePorts : Fin 8 → Fin 24 := ![7,8,9,10,11,12,13,14]
def paddingPorts : Fin 3 → Fin 24 := ![22,8,23]
def emitPorts : Fin 6 → Fin 24 := ![15,8,5,16,17,18]

theorem exponentRegs_injective : Function.Injective exponentRegs := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 8 => x.val) h
theorem exponentPorts_injective : Function.Injective exponentPorts := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 24 => x.val) h
theorem coordinatePorts_injective : Function.Injective coordinatePorts := by decide
theorem paddingPorts_injective : Function.Injective paddingPorts := by decide
theorem emitPorts_injective : Function.Injective emitPorts := by decide

abbrev exponent : Cmd 8 24 := .call
  (ProgramLinking.liftProgram SubexpExponentGather.program exponentRegs exponentPorts)
abbrev coordinate : Cmd 8 24 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1) id coordinatePorts)
abbrev paddingCore : Cmd 8 24 := .call
  (ProgramLinking.liftProgram ModularPrograms.paddingLEProgram id paddingPorts)
abbrev padding : Cmd 8 24 :=
  .seq (.call (StackRoutines.copyProgram 21 22 23 (0 : Fin 8) 1))
    (.seq paddingCore
      (.seq (.call (StackRoutines.transferProgram 22 23 (0 : Fin 8) 1))
        (.call (StackRoutines.transferProgram 23 8 (0 : Fin 8) 1))))
abbrev emit : Cmd 8 24 := .call
  (ProgramLinking.liftProgram SubexpWeightEmit.program id emitPorts)

abbrev normalize : Cmd 8 24 :=
  .seq (RecordPrograms.atom (.set 0 false))
    (.seq (RecordPrograms.atom (.set 1 true)) (RecordPrograms.atom (.set 7 false)))

/-- Three copies of each support index drive the two actual lookups and the
serialized index field. The payload itself is consumed before continuation. -/
abbrev callback : Cmd 8 24 :=
  .seq (.call (StackRoutines.copyProgram 20 2 4 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.copyProgram 20 9 4 (0 : Fin 8) 1))
      (.seq (.call (StackRoutines.transferProgram 20 15 (0 : Fin 8) 1))
        (.seq exponent (.seq coordinate (.seq padding (.seq emit normalize))))))

abbrev command : Cmd 8 24 := RecordPrograms.iterate ports callback
def program := StructuredCalls.compiled command (19 : Fin 24) 16

/-- The table size is independent of dimension, support size, and word widths. -/
theorem control_size : StructuredCalls.size command = 200 := by decide

def afterExponent (d : Data) (bits : List Bool) : Data :=
  ⟨fun j => if j.val < 3 then false else d.regs j,
    Function.update (Function.update d.stacks 2 []) 5 bits⟩

theorem exponent_eval {D : ℕ} (d : Data) (a : Fin D → ℕ) (i : Fin D)
    (hmaster : d.stacks 0 = SymbolicCost.unaryWords (List.ofFn a))
    (hindex : d.stacks 2 = List.replicate i.val true)
    (hwork : ∀ j : Fin 7, j ≠ 0 → j ≠ 2 → d.stacks (exponentPorts j) = []) :
    ∃ n ≤ SubexpExponentGather.gatherBudget ((List.ofFn a).take i.val) (a i)
        ((List.ofFn a).drop (i.val+1))+1, ∃ bits,
      Eval exponent n d (afterExponent d bits) ∧
      BinaryArithmetic.toNat bits = a i ∧ bits.length ≤ a i := by
  let rr := fun j => d.regs (exponentRegs j)
  obtain ⟨bits,⟨n,hn,ht⟩,hv,hl⟩ := SubexpExponentGather.gather_index_runs rr a i
  let before := SubexpExponentGather.st rr (SymbolicCost.unaryWords (List.ofFn a)) []
    (List.replicate i.val true) [] [] [] []
  let after := SubexpExponentGather.st (fun _ => false)
    (SymbolicCost.unaryWords (List.ofFn a)) [] [] [] [] bits []
  have hbefore : embedState exponentRegs exponentPorts d before = d := by
    apply embedState_eq _ _ exponentRegs_injective exponentPorts_injective
    · intro j; rfl
    · intro j
      fin_cases j
      · exact hmaster
      · exact hwork 1 (by decide) (by decide)
      · exact hindex
      · exact hwork 3 (by decide) (by decide)
      · exact hwork 4 (by decide) (by decide)
      · exact hwork 5 (by decide) (by decide)
      · exact hwork 6 (by decide) (by decide)
    · intros; rfl
    · intros; rfl
  have hafter : embedState exponentRegs exponentPorts d after = afterExponent d bits := by
    apply embedState_eq _ _ exponentRegs_injective exponentPorts_injective
    · intro j
      fin_cases j <;> simp [afterExponent,exponentRegs,after,SubexpExponentGather.st]
    · intro j
      fin_cases j
      · simpa [afterExponent,exponentPorts,SubexpExponentGather.st,after] using hmaster
      · simpa [afterExponent,exponentPorts,SubexpExponentGather.st,after] using hwork 1 (by decide) (by decide)
      · rfl
      · simpa [afterExponent,exponentPorts,SubexpExponentGather.st,after] using hwork 3 (by decide) (by decide)
      · simpa [afterExponent,exponentPorts,SubexpExponentGather.st,after] using hwork 4 (by decide) (by decide)
      · rfl
      · simpa [afterExponent,exponentPorts,SubexpExponentGather.st,after] using hwork 6 (by decide) (by decide)
    · intro j hj
      have hlarge : ¬ j.val < 3 := by
        intro hsmall
        exact hj ⟨⟨j.val,hsmall⟩,Fin.ext rfl⟩
      simp [afterExponent,hlarge]
    · intro j hj
      have h2 : j ≠ 2 := fun h => hj ⟨2,by simpa [exponentPorts] using h.symm⟩
      have h5 : j ≠ 5 := fun h => hj ⟨5,by simpa [exponentPorts] using h.symm⟩
      simp [afterExponent,h2,h5]
  have h := eval_call_lifted SubexpExponentGather.program exponentRegs exponentPorts d
    exponentRegs_injective exponentPorts_injective (a := before) (b := after) ht
  exact ⟨n,hn,bits,by simpa only [exponent,hbefore,hafter] using h,hv,hl⟩

def afterCoordinate (d : Data) (record : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 9 []) 8 (record++d.stacks 8)⟩

theorem coordinate_eval (d : Data) (earlier : List (List Bool))
    (record rest width index : List Bool)
    (hsource : d.stacks 7 = earlier.flatten++(record++rest))
    (hw : d.stacks 10 = width) (hi : d.stacks 9 = index)
    (hlen : index.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = width.length)
    (hr : record.length = width.length)
    (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = [])
    (h13 : d.stacks 13 = []) (h14 : d.stacks 14 = []) :
    Eval coordinate (earlier.length*(14*width.length+10)+15*width.length+16)
      d (afterCoordinate d record) := by
  let localStacks := fun j => d.stacks (coordinatePorts j)
  let before : State 8 8 := ⟨d.regs,localStacks⟩
  let after : State 8 8 := ⟨readRegs d.regs 0 1 none,
    ArrayUpdatePrograms.readStacks record localStacks⟩
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    earlier record rest width index d.regs localStacks hsource hw hi hlen hrows hr h11 h12 h13 h14
  have hb : embedState id coordinatePorts d before = d := by
    apply embedState_eq _ _ Function.injective_id coordinatePorts_injective
    · intro j; rfl
    · intro j; rfl
    · intros; rfl
    · intros; rfl
  have ha : embedState id coordinatePorts d after = afterCoordinate d record := by
    apply embedState_eq _ _ Function.injective_id coordinatePorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;>
        simp [afterCoordinate,coordinatePorts,after,localStacks,ArrayUpdatePrograms.readStacks]
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨1,by simpa [coordinatePorts] using h.symm⟩
      have h9 : j ≠ 9 := fun h => hj ⟨2,by simpa [coordinatePorts] using h.symm⟩
      simp [afterCoordinate,h8,h9]
  have h := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id coordinatePorts d Function.injective_id coordinatePorts_injective (a := before) (b := after) ht
  simpa only [coordinate,hb,ha] using h

def afterPaddingCore (d : Data) (regs : Fin 8 → Bool) : Data :=
  ⟨regs,Function.update (Function.update d.stacks 8 []) 22
    (ModularArithmetic.padTo (d.stacks 22) (d.stacks 8))⟩

theorem paddingCore_eval (d : Data) (h23 : d.stacks 23 = [])
    (hlen : (d.stacks 8).length ≤ (d.stacks 22).length) :
    ∃ regs, Eval paddingCore (7*(d.stacks 22).length+6) d (afterPaddingCore d regs) := by
  obtain ⟨regs,ht,_⟩ := ModularPrograms.paddingLE_correct d.regs
    (d.stacks 22) (d.stacks 8) hlen
  let before : State 8 3 :=
    ⟨d.regs,ModularPrograms.operandStacks (d.stacks 22) (d.stacks 8) []⟩
  let after : State 8 3 :=
    ⟨regs,ModularPrograms.operandStacks
      (ModularArithmetic.padTo (d.stacks 22) (d.stacks 8)) [] []⟩
  have hb : embedState id paddingPorts d before = d := by
    apply embedState_eq _ _ Function.injective_id paddingPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;> simp [before,paddingPorts,ModularPrograms.operandStacks,h23]
    · intros; rfl
    · intros; rfl
  have ha : embedState id paddingPorts d after = afterPaddingCore d regs := by
    apply embedState_eq _ _ Function.injective_id paddingPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;>
        simp [after,afterPaddingCore,paddingPorts,ModularPrograms.operandStacks,h23]
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨1,by simpa [paddingPorts] using h.symm⟩
      have h22 : j ≠ 22 := fun h => hj ⟨0,by simpa [paddingPorts] using h.symm⟩
      simp [afterPaddingCore,h8,h22]
  have h := eval_call_lifted ModularPrograms.paddingLEProgram id paddingPorts d
    Function.injective_id paddingPorts_injective (a := before) (b := after) ht
  exact ⟨regs,by simpa only [paddingCore,hb,ha] using h⟩

def afterPadding (d : Data) (regs : Fin 8 → Bool) : Data :=
  ⟨regs,Function.update d.stacks 8
    (ModularArithmetic.padTo (d.stacks 21) (d.stacks 8))⟩

/-- Padding reads a copy of the target-width master and restores both scratch
stacks. The selected coordinate remains in little-endian order. -/
theorem padding_eval (d : Data) (h22 : d.stacks 22 = []) (h23 : d.stacks 23 = [])
    (hlen : (d.stacks 8).length ≤ (d.stacks 21).length) :
    ∃ regs, Eval padding (20*(d.stacks 21).length+17) d (afterPadding d regs) := by
  let d₁ := afterCopy d 21 22 0 1
  have hc := copy_eval d 21 22 23 0 1 (by decide) (by decide) (by decide) (by decide) h23
  obtain ⟨regs,hp⟩ := paddingCore_eval d₁
    (by simp [d₁,afterCopy,StackRoutines.copyStacks,h23])
    (by simpa [d₁,afterCopy,StackRoutines.copyStacks,h22] using hlen)
  let d₂ := afterPaddingCore d₁ regs
  let d₃ := afterTransfer d₂ 22 23 0 1
  let d₄ := afterTransfer d₃ 23 8 0 1
  have ht := transfer_eval d₂ 22 23 0 1 (by decide) (by decide)
  have hu := transfer_eval d₃ 23 8 0 1 (by decide) (by decide)
  have he : d₄ = afterPadding d d₄.regs := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;>
        simp [d₄,d₃,d₂,d₁,afterTransfer,afterCopy,afterPaddingCore,afterPadding,
          StackRoutines.copyStacks,StackRoutines.transferStacks,h22,h23]
  have hrun := Eval.seq hc (Eval.seq hp (Eval.seq ht hu))
  change afterTransfer d₃ 23 8 0 1 = afterPadding d d₄.regs at he
  rw [he] at hrun
  refine ⟨d₄.regs,?_⟩
  have hcopyLength : (d₁.stacks 22).length = (d.stacks 21).length := by
    simp [d₁, afterCopy, StackRoutines.copyStacks, h22]
  have hpaddingLength : (d₂.stacks 22).length = (d.stacks 21).length := by
    simp [d₂, d₁, afterPaddingCore, afterCopy, StackRoutines.copyStacks, h22,
      ModularArithmetic.padTo_length]
  have htransferLength : (d₃.stacks 23).length = (d.stacks 21).length := by
    simp [d₃, d₂, d₁, afterTransfer, afterPaddingCore, afterCopy,
      StackRoutines.copyStacks, StackRoutines.transferStacks, h22, h23,
      ModularArithmetic.padTo_length]
  rw [hcopyLength, hpaddingLength, htransferLength] at hrun
  have hcost : (7 * (d.stacks 21).length + 5) +
      ((7 * (d.stacks 21).length + 6) +
        ((3 * (d.stacks 21).length + 3) + (3 * (d.stacks 21).length + 3))) =
      20 * (d.stacks 21).length + 17 := by
    omega
  rw [hcost] at hrun
  exact hrun

def afterEmit (d : Data) : Data :=
  ⟨SubexpWeightEmit.finishedRegs d.regs,
    Function.update (Function.update (Function.update (Function.update d.stacks 15 []) 8 []) 5 [])
      16 (SubexpWeightEmit.recordBits (d.stacks 15) (d.stacks 8) (d.stacks 5) ++ d.stacks 16)⟩

theorem emit_eval (d : Data) (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) :
    Eval emit (14*(d.stacks 15).length+5*(d.stacks 8).length+5*(d.stacks 5).length+31)
      d (afterEmit d) := by
  let before := SubexpWeightEmit.state d.regs (d.stacks 15) (d.stacks 8) (d.stacks 5) (d.stacks 16)
  let after := SubexpWeightEmit.state (SubexpWeightEmit.finishedRegs d.regs) [] [] []
    (SubexpWeightEmit.recordBits (d.stacks 15) (d.stacks 8) (d.stacks 5) ++ d.stacks 16)
  have hb : embedState id emitPorts d before = d := by
    apply embedState_eq _ _ Function.injective_id emitPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;> simp [before,SubexpWeightEmit.state,emitPorts,h17,h18]
    · intros; rfl
    · intros; rfl
  have ha : embedState id emitPorts d after = afterEmit d := by
    apply embedState_eq _ _ Function.injective_id emitPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;> simp [after,afterEmit,SubexpWeightEmit.state,emitPorts,h17,h18]
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      have h15 : j ≠ 15 := fun h => hj ⟨0,by simpa [emitPorts] using h.symm⟩
      have h8 : j ≠ 8 := fun h => hj ⟨1,by simpa [emitPorts] using h.symm⟩
      have h5 : j ≠ 5 := fun h => hj ⟨2,by simpa [emitPorts] using h.symm⟩
      have h16 : j ≠ 16 := fun h => hj ⟨3,by simpa [emitPorts] using h.symm⟩
      simp [afterEmit,h15,h8,h5,h16]
  have ht := SubexpWeightEmit.program_trace d.regs (d.stacks 15) (d.stacks 8)
    (d.stacks 5) (d.stacks 16)
  have h := eval_call_lifted SubexpWeightEmit.program id emitPorts d
    Function.injective_id emitPorts_injective (a := before) (b := after) ht
  simpa only [emit,hb,ha] using h

def normalized (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 true) 7 false

theorem normalize_eval (d : Data) :
    Eval normalize 3 d ⟨normalized d.regs,d.stacks⟩ := by
  have h₀ := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 8) true)
    ((StructuredProgram.Atom.set 0 false).eval d))
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set (7 : Fin 8) false)
    ((StructuredProgram.Atom.set 1 true).eval ((StructuredProgram.Atom.set 0 false).eval d)))
  simpa [normalize,RecordPrograms.atom,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,
    execInstr,normalized] using Eval.seq h₀ (Eval.seq h₁ h₂)

def callbackBudget {D : ℕ} (a : Fin D → ℕ) (width target : List Bool) (i : Fin D) : ℕ :=
  SubexpExponentGather.gatherBudget ((List.ofFn a).take i.val) (a i)
    ((List.ofFn a).drop (i.val+1)) +
      i.val*(14*width.length+10)+40*i.val+15*width.length+25*target.length+5*a i+120

theorem callback_eval {D : ℕ} (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target source output : List Bool) (i : Fin D)
    (hwidth : ∀ j, (coordinates j).length = width.length)
    (hpad : width.length ≤ target.length) :
    ∃ n ≤ callbackBudget a width target i, ∃ regs' bits,
      Eval callback n
        (state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
          width target source output (List.replicate i.val true))
        (state (normalized regs') (SymbolicCost.unaryWords (List.ofFn a))
          (List.ofFn coordinates).flatten width target source
          (SubexpWeightEmit.recordBits (List.replicate i.val true) (ModularArithmetic.padTo target (coordinates i)) bits++output) []) ∧
      BinaryArithmetic.toNat bits = a i ∧ bits.length ≤ a i := by
  let d₀ := state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
    width target source output (List.replicate i.val true)
  let d₁ := afterCopy d₀ 20 2 0 1
  let d₂ := afterCopy d₁ 20 9 0 1
  let d₃ := afterTransfer d₂ 20 15 0 1
  have h₁ := copy_eval d₀ 20 2 4 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have h₂ := copy_eval d₁ 20 9 4 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d₁,d₀,afterCopy,StackRoutines.copyStacks,state])
  have h₃ := transfer_eval d₂ 20 15 0 1 (by decide) (by decide)
  have hm : d₃.stacks 0 = SymbolicCost.unaryWords (List.ofFn a) := by
    simp [d₃,d₂,d₁,d₀,afterTransfer,afterCopy,StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hi : d₃.stacks 2 = List.replicate i.val true := by
    simp [d₃,d₂,d₁,d₀,afterTransfer,afterCopy,StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hw : ∀ j : Fin 7, j ≠ 0 → j ≠ 2 → d₃.stacks (exponentPorts j) = [] := by
    intro j h0 h2
    fin_cases j <;> simp_all [d₃,d₂,d₁,d₀,exponentPorts,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  obtain ⟨ne,hne,bits,he,hvalue,hlen⟩ := exponent_eval d₃ a i hm hi hw
  let d₄ := afterExponent d₃ bits
  let earlier := (List.ofFn coordinates).take i.val
  let rest := ((List.ofFn coordinates).drop (i.val+1)).flatten
  have hcSource : d₄.stacks 7 = earlier.flatten++(coordinates i++rest) := by
    calc
      d₄.stacks 7 = (List.ofFn coordinates).flatten := by
        simp [d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
          StackRoutines.transferStacks,StackRoutines.copyStacks,state]
      _ = earlier.flatten++(coordinates i++rest) := by
        simpa [earlier,rest,List.flatten_append,List.flatten_cons] using
          congrArg List.flatten (SubexpExponentGather.ofFn_decomposition coordinates i)
  have hcWidth : d₄.stacks 10 = width := by
    simp [d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hcIndex : d₄.stacks 9 = List.replicate i.val true := by
    simp [d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hearlier : earlier.length = i.val := SubexpExponentGather.ofFn_prefix_length coordinates i
  have hrows : ∀ row ∈ earlier, row.length = width.length := by
    intro row hrow
    have hh : row ∈ List.ofFn coordinates := List.mem_of_mem_take hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hh
    exact hwidth j
  have hclean : ∀ j ∈ ([11,12,13,14] : List (Fin 24)), d₄.stacks j = [] := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl <;>
      simp [d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
        StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hc := coordinate_eval d₄ earlier (coordinates i) rest width (List.replicate i.val true)
    hcSource hcWidth hcIndex (by simp [hearlier]) hrows (hwidth i)
    (hclean 11 (by simp)) (hclean 12 (by simp)) (hclean 13 (by simp)) (hclean 14 (by simp))
  let d₅ := afterCoordinate d₄ (coordinates i)
  have h22 : d₅.stacks 22 = [] := by
    simp [d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have h23 : d₅.stacks 23 = [] := by
    simp [d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hpadLength : (d₅.stacks 8).length ≤ (d₅.stacks 21).length := by
    simpa [d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state,hwidth] using hpad
  obtain ⟨rp,hp⟩ := padding_eval d₅ h22 h23 hpadLength
  let d₅p := afterPadding d₅ rp
  have h17 : d₅p.stacks 17 = [] := by
    simp [d₅p,afterPadding,d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have h18 : d₅p.stacks 18 = [] := by
    simp [d₅p,afterPadding,d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have hem := emit_eval d₅p h17 h18
  let d₆ := afterEmit d₅p
  have hz := normalize_eval d₆
  have hfinal : (⟨normalized d₆.regs,d₆.stacks⟩ : Data) =
      state (normalized d₆.regs) (SymbolicCost.unaryWords (List.ofFn a))
        (List.ofFn coordinates).flatten width target source
        (SubexpWeightEmit.recordBits (List.replicate i.val true)
          (ModularArithmetic.padTo target (coordinates i)) bits++output) [] := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;>
        simp [d₆,afterEmit,d₅p,afterPadding,d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,
          afterCopy,StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  rw [hfinal] at hz
  have hlen₀ : (d₀.stacks 20).length = i.val := by simp [d₀,state]
  have hlen₁ : (d₁.stacks 20).length = i.val := by
    simp [d₁,d₀,afterCopy,StackRoutines.copyStacks,state]
  have hlen₂ : (d₂.stacks 20).length = i.val := by
    simp [d₂,d₁,d₀,afterCopy,StackRoutines.copyStacks,state]
  have h21 : (d₅.stacks 21).length = target.length := by
    simp [d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have h15 : (d₅p.stacks 15).length = i.val := by
    simp [d₅p,afterPadding,d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state]
  have h8 : (d₅p.stacks 8).length = target.length := by
    simp [d₅p,afterPadding,d₅,afterCoordinate,d₄,afterExponent,d₃,d₂,d₁,d₀,afterTransfer,afterCopy,
      StackRoutines.transferStacks,StackRoutines.copyStacks,state,ModularArithmetic.padTo_length]
  have h5 : (d₅p.stacks 5).length = bits.length := by
    simp [d₅p,afterPadding,d₅,afterCoordinate,d₄,afterExponent]
  have hrun := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃
    (Eval.seq he (Eval.seq hc (Eval.seq hp (Eval.seq hem hz))))))
  simp only [hlen₀,hlen₁,hlen₂,hearlier,h21,h15,h8,h5] at hrun
  refine ⟨_,?_,d₆.regs,bits,hrun,hvalue,hlen⟩
  unfold callbackBudget
  omega

def withFlags (regs : Fin 8 → Bool) (v pr f : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 v) 1 pr) 7 f

@[simp] theorem outer_state (regs : Fin 8 → Bool)
    (exponents coordinates width target source output payload : List Bool)
    (v pr f : Bool) (source' payload' : List Bool) :
    RecordPrograms.state ports (state regs exponents coordinates width target source output payload)
      v pr f source' payload' =
      state (withFlags regs v pr f) exponents coordinates width target source' output payload' := by
  apply state_ext
  · rfl
  · funext j; fin_cases j <;> simp [RecordPrograms.state, ports, state]

@[simp] theorem withFlags_self (regs : Fin 8 → Bool) :
    withFlags regs (regs 0) (regs 1) (regs 7) = regs := by
  funext j; fin_cases j <;> simp [withFlags]

def supportBits {D : ℕ} (support : List (Fin D)) : List (List Bool) :=
  support.map (fun i => List.replicate i.val true)

def supportBudget {D : ℕ} (a : Fin D → ℕ) (width target : List Bool) (support : List (Fin D)) : ℕ :=
  (support.map (fun i => 6*i.val+callbackBudget a width target i+7)).sum

def GoodRecord {D : ℕ} (a : Fin D → ℕ) (coordinates : Fin D → List Bool) (target : List Bool)
    (i : Fin D) (record : SubexpWeightControl.WeightRecord) : Prop :=
  record.index = List.replicate i.val true ∧ record.base = ModularArithmetic.padTo target (coordinates i) ∧
    BinaryArithmetic.toNat record.exponent = a i ∧ record.exponent.length ≤ a i

theorem GoodRecord.base_length {D : ℕ} {a : Fin D → ℕ}
    {coordinates : Fin D → List Bool} {target : List Bool}
    {i : Fin D} {record : SubexpWeightControl.WeightRecord}
    (h : GoodRecord a coordinates target i record) : record.base.length = target.length := by
  rw [h.2.1,ModularArithmetic.padTo_length]

theorem GoodRecord.base_value {D : ℕ} {a : Fin D → ℕ}
    {coordinates : Fin D → List Bool} {target : List Bool}
    {i : Fin D} {record : SubexpWeightControl.WeightRecord}
    (h : GoodRecord a coordinates target i record)
    (hlen : (coordinates i).length ≤ target.length) :
    BinaryArithmetic.toNat record.base = BinaryArithmetic.toNat (coordinates i) := by
  rw [h.2.1,ModularArithmetic.padTo_correct target (coordinates i) hlen]

def base {D : ℕ} (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target : List Bool)
    (built : List SubexpWeightControl.WeightRecord) (suffix : List Bool) : Data :=
  state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten
    width target [] (SubexpWeightControl.encodeRecords built++suffix) []

theorem loop_eval {D : ℕ} (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target sourceSuffix outputSuffix : List Bool)
    (hwidth : ∀ j, (coordinates j).length = width.length)
    (hpad : width.length ≤ target.length)
    (support : List (Fin D)) (built : List SubexpWeightControl.WeightRecord) :
    ∃ n ≤ 1+supportBudget a width target support, ∃ regs' records,
      List.Forall₂ (GoodRecord a coordinates target) support.reverse records ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (base regs a coordinates width target built outputSuffix)
          (supportBits support) sourceSuffix)
        (RecordPrograms.state ports (base regs' a coordinates width target (records++built) outputSuffix)
          false true false sourceSuffix []) := by
  induction support generalizing regs built with
  | nil =>
      refine ⟨1,by simp [supportBudget],regs,[],List.Forall₂.nil,?_⟩
      apply Eval.while_false
      simp [RecordPrograms.afterTag,supportBits]
  | cons i support ih =>
      let tail := Encoding.encodeList id (supportBits support)++sourceSuffix
      let out := SubexpWeightControl.encodeRecords built++outputSuffix
      have hp := RecordPrograms.reader_eval ports (base regs a coordinates width target built outputSuffix)
        (List.replicate i.val true) tail [] true true false
      obtain ⟨n,hn,rm,bits,hc,hv,hl⟩ := callback_eval (withFlags regs false true false)
        a coordinates width target tail out i hwidth hpad
      let record : SubexpWeightControl.WeightRecord := ⟨List.replicate i.val true,ModularArithmetic.padTo target (coordinates i),bits⟩
      have hgood : GoodRecord a coordinates target i record := ⟨rfl,rfl,hv,hl⟩
      have hcallback : Eval callback n
          (RecordPrograms.state ports (base regs a coordinates width target built outputSuffix)
            false true false tail (List.replicate i.val true).reverse)
          (RecordPrograms.state ports (base rm a coordinates width target (record::built) outputSuffix)
            false true false tail []) := by
        simpa only [base,outer_state,List.reverse_replicate,normalized,withFlags,record,out,
          SubexpWeightEmit.recordBits,SubexpWeightControl.encodeRecords,SubexpWeightControl.payload,
          List.cons_append,List.append_assoc] using hc
      have hparse : Eval (RecordPrograms.reader ports) (6*i.val+4)
          (RecordPrograms.afterTag ports (base regs a coordinates width target built outputSuffix)
            (supportBits (i::support)) sourceSuffix)
          (RecordPrograms.state ports (base regs a coordinates width target built outputSuffix)
            false true false tail (List.replicate i.val true).reverse) := by
        simpa [RecordPrograms.afterTag,supportBits,tail] using hp
      have hb : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports (base rm a coordinates width target (record::built) outputSuffix)
            false true false tail [])
          (RecordPrograms.afterTag ports (base rm a coordinates width target (record::built) outputSuffix)
            (supportBits support) sourceSuffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports (base rm a coordinates width target (record::built) outputSuffix)
          (supportBits support) sourceSuffix false true
      obtain ⟨m,hm,rf,records,hrecords,hr⟩ := ih (regs := rm) (built := record::built)
      have hguard : (RecordPrograms.afterTag ports (base regs a coordinates width target built outputSuffix)
          (supportBits (i::support)) sourceSuffix).regs ports.tag = true := by
        simp [RecordPrograms.afterTag,supportBits]
      have hrun := Eval.while_true hguard (Eval.seq hparse (Eval.seq hcallback hb)) hr
      refine ⟨(6*i.val+4+(n+2))+m+1,?_,rf,records++[record],?_,?_⟩
      · simp only [supportBudget,List.map_cons,List.sum_cons] at hm ⊢
        omega
      · simpa only [List.reverse_cons] using
          List.rel_append hrecords (List.Forall₂.cons hgood List.Forall₂.nil)
      · simpa [RecordPrograms.loop,RecordPrograms.body,List.append_assoc] using hrun

theorem command_eval {D : ℕ} (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target sourceSuffix outputSuffix : List Bool)
    (hwidth : ∀ j, (coordinates j).length = width.length)
    (hpad : width.length ≤ target.length) (support : List (Fin D)) :
    ∃ n ≤ 3+supportBudget a width target support, ∃ regs' records,
      List.Forall₂ (GoodRecord a coordinates target) support.reverse records ∧
      Eval command n
        (state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten width target
          (Encoding.encodeList id (supportBits support)++sourceSuffix)
          (SubexpWeightControl.encodeRecords []++outputSuffix) [])
        (state (withFlags regs' false true false) (SymbolicCost.unaryWords (List.ofFn a))
          (List.ofFn coordinates).flatten width target sourceSuffix
          (SubexpWeightControl.encodeRecords records++outputSuffix) []) := by
  obtain ⟨n,hn,regs',records,hrecords,hr⟩ :=
    loop_eval regs a coordinates width target sourceSuffix outputSuffix hwidth hpad support []
  have hs := RecordPrograms.set_found_eval ports (base regs a coordinates width target [] outputSuffix)
    (regs 0) (regs 1) (regs 7) false (Encoding.encodeList id (supportBits support)++sourceSuffix) []
  have hp := RecordPrograms.pop_list_eval ports (base regs a coordinates width target [] outputSuffix)
    (supportBits support) sourceSuffix (regs 0) (regs 1)
  refine ⟨1+(1+n),by omega,regs',records,hrecords,?_⟩
  simpa only [command,RecordPrograms.iterate,base,outer_state,withFlags_self,List.append_nil]
    using Eval.seq hs (Eval.seq hp hr)

theorem program_runs {D : ℕ} (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target sourceSuffix outputSuffix : List Bool)
    (hwidth : ∀ j, (coordinates j).length = width.length)
    (hpad : width.length ≤ target.length) (support : List (Fin D)) :
    ∃ regs' records, List.Forall₂ (GoodRecord a coordinates target) support.reverse records ∧
      RunsIn program (4+supportBudget a width target support)
        ((state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten width target
          (Encoding.encodeList id (supportBits support)++sourceSuffix)
          (SubexpWeightControl.encodeRecords []++outputSuffix) []).withPC (some program.entry))
        ((state (withFlags regs' false true false) (SymbolicCost.unaryWords (List.ofFn a))
          (List.ofFn coordinates).flatten width target sourceSuffix
          (SubexpWeightControl.encodeRecords records++outputSuffix) []).withPC none) := by
  obtain ⟨n,hn,regs',records,hrecords,hr⟩ := command_eval regs a coordinates width target
    sourceSuffix outputSuffix hwidth hpad support
  exact ⟨regs',records,hrecords,n+1,by omega,StructuredCalls.compiled_halt_trace hr 19 16⟩

theorem program_primitive_runs {D : ℕ} (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target sourceSuffix outputSuffix : List Bool)
    (hwidth : ∀ j, (coordinates j).length = width.length)
    (hpad : width.length ≤ target.length) (support : List (Fin D)) :
    ∃ regs' records, List.Forall₂ (GoodRecord a coordinates target) support.reverse records ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program*(4+supportBudget a width target support))
        (BitProgram.primitiveCfg program
          ((state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten width target
            (Encoding.encodeList id (supportBits support)++sourceSuffix)
            (SubexpWeightControl.encodeRecords []++outputSuffix) []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((state (withFlags regs' false true false) (SymbolicCost.unaryWords (List.ofFn a))
            (List.ofFn coordinates).flatten width target sourceSuffix
            (SubexpWeightControl.encodeRecords records++outputSuffix) []).withPC none)) := by
  obtain ⟨regs',records,hrecords,hr⟩ :=
    program_runs regs a coordinates width target sourceSuffix outputSuffix hwidth hpad support
  exact ⟨regs',records,hrecords,BitProgram.primitive_execution program hr⟩

theorem program_runs_lifted {D R S : ℕ}
    (register : Fin 8 → Fin R) (stack : Fin 24 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (ambient : Cfg R S (StructuredCalls.size command+1))
    (regs : Fin 8 → Bool) (a : Fin D → ℕ)
    (coordinates : Fin D → List Bool) (width target sourceSuffix outputSuffix : List Bool)
    (hwidth : ∀ j, (coordinates j).length = width.length)
    (hpad : width.length ≤ target.length) (support : List (Fin D)) :
    ∃ regs' records, List.Forall₂ (GoodRecord a coordinates target) support.reverse records ∧
      RunsIn (ProgramLinking.liftProgram program register stack)
        (4+supportBudget a width target support)
        (ProgramLinking.embedCfg register stack id none ambient
          ((state regs (SymbolicCost.unaryWords (List.ofFn a)) (List.ofFn coordinates).flatten width target
            (Encoding.encodeList id (supportBits support)++sourceSuffix)
            (SubexpWeightControl.encodeRecords []++outputSuffix) []).withPC (some program.entry)))
        (ProgramLinking.embedCfg register stack id none ambient
          ((state (withFlags regs' false true false) (SymbolicCost.unaryWords (List.ofFn a))
            (List.ofFn coordinates).flatten width target sourceSuffix
            (SubexpWeightControl.encodeRecords records++outputSuffix) []).withPC none)) := by
  obtain ⟨regs',records,hrecords,h⟩ :=
    program_runs regs a coordinates width target sourceSuffix outputSuffix hwidth hpad support
  exact ⟨regs',records,hrecords,ProgramLinking.liftProgram_runsIn program register stack ambient hr hs h⟩

end SubexponentialSAT.SubexpWeightGather

end OAI.Algorithms
