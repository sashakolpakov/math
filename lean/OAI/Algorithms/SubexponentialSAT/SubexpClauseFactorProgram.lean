import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer
import OAI.Algorithms.SubexponentialSAT.SubexpFieldTableEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Physical construction of one clause factor

The preserved input ports contain the field modulus, declared-variable shape,
padded-array shape, chunk width in unary and binary, encoded clause, and field
word width. The produced scope uses stable last-occurrence order; the table
contains Boolean values in descending local scalar-rank order.
-/

namespace SubexponentialSAT.SubexpClauseFactorProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 11 31

structure Inputs where
  modulus : List Bool
  nShape : List Bool
  fullShape : List Bool
  ellShape : List Bool
  clause : List Bool
  widthShape : List Bool
  binaryEll : List Bool

def tapes (c : Inputs) (exponent rank arity scope fuel output : List Bool) :
    Fin 31 → List Bool := fun i =>
  if i = 0 then exponent else if i = 18 then c.modulus else if i = 19 then rank
  else if i = 20 then arity else if i = 21 then c.nShape else if i = 22 then c.fullShape
  else if i = 23 then c.ellShape else if i = 24 then scope else if i = 25 then c.clause
  else if i = 26 then c.widthShape else if i = 27 then fuel else if i = 29 then output
  else if i = 30 then c.binaryEll else []

def data (regs : Fin 11 → Bool) (c : Inputs)
    (exponent rank arity scope fuel output : List Bool) : Data :=
  ⟨regs, tapes c exponent rank arity scope fuel output⟩

def zeroRegs : Fin 11 → Bool := fun _ => false

structure Valid {n : ℕ} (c : Inputs) (D : ℕ)
    (ls : List (SAT.Literal (Fin n))) : Prop where
  modulus_pos : 0 < BinaryArithmetic.toNat c.modulus
  ell_pos : 0 < BinaryArithmetic.toNat c.binaryEll
  ell_value : BinaryArithmetic.toNat c.binaryEll = c.ellShape.length
  width : c.widthShape.length = c.modulus.length
  ell_width : c.ellShape.length ≤ c.widthShape.length
  full : c.fullShape.length = D * c.ellShape.length
  shape : c.nShape.length = n
  covered : n ≤ c.fullShape.length
  clause : c.clause = SubexpClauseRowProgram.clauseBytes ls

def codes {n : ℕ} (ls : List (SAT.Literal (Fin n))) : List ℕ :=
  ls.map Encoding.literalCode

def rawScope {n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n))) : List ℕ :=
  SubexpScopeProducer.scope c.binaryEll (codes ls)

def scopeBytes {n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n))) : List Bool :=
  Encoding.encodeList Encoding.encodeNat (rawScope c ls)

theorem scopeBound {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) :
    ∀ j ∈ SubexpScopeProducer.scope c.binaryEll (codes ls), j < D := by
  apply SubexpScopeProducer.scope_lt c.binaryEll (codes ls) hv.ell_pos
  · simpa only [hv.ell_value, ← hv.full] using hv.covered
  · intro code hc
    obtain ⟨literal, _, rfl⟩ := List.mem_map.mp hc
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
    simpa only [Nat.mul_comm] using Encoding.literalCode_lt literal

/-- This view retains the exact scope order emitted by the physical producer. -/
def scopeOf {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) : List (Fin D) :=
  SubexpScopeProducer.typedScope c.binaryEll (codes ls) (scopeBound c ls hv)

theorem scopeOf_values {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) :
    (scopeOf c ls hv).map Fin.val = SubexpScopeProducer.scope c.binaryEll (codes ls) :=
  SubexpScopeProducer.typedScope_values _ _ _

theorem scopeOf_nodup {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) : (scopeOf c ls hv).Nodup :=
  SubexpScopeProducer.typedScope_nodup _ _ _

theorem scopeOf_length_le {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) : (scopeOf c ls hv).length ≤ ls.length := by
  rw [scopeOf, SubexpScopeProducer.typedScope_length]
  exact (SubexpScopeProducer.scope_length_le _ _).trans_eq (List.length_map ..)

theorem scopeBytes_length_le {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) : (scopeBytes c ls).length ≤ 1 + (2 * D + 2) * ls.length := by
  have h := Encoding.length_encodeList_upper Encoding.encodeNat (rawScope c ls) D (by
    intro j hj
    rw [Encoding.length_encodeNat]
    have hjlt := scopeBound c ls hv j hj
    omega)
  have hlen : (rawScope c ls).length ≤ ls.length :=
    (SubexpScopeProducer.scope_length_le _ _).trans_eq (List.length_map ..)
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) _)

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

abbrev reset : Cmd 11 31 := RegisterResetProgram.all

theorem reset_eval (d : Data) : Eval reset 11 d ⟨zeroRegs, d.stacks⟩ :=
  RegisterResetProgram.all_eval d

abbrev copyClause : Cmd 11 31 := .call (copyProgram 25 24 1 0 1)

theorem copyClause_eval (c : Inputs) :
    Eval copyClause (7 * c.clause.length + 5)
      (data zeroRegs c [] [] [] [] [] [])
      (data zeroRegs c [] [] [] c.clause [] []) := by
  have h := ListRegisterProgram.copy_run (25 : Fin 31) 24 1 (0 : Fin 11) 1
    (by decide) (by decide) (by decide) (by decide)
    zeroRegs (tapes c [] [] [] [] [] []) rfl
  have hr : readRegs zeroRegs 0 1 none = zeroRegs := by
    funext i; fin_cases i <;> rfl
  have hs : copyStacks 25 24 (tapes c [] [] [] [] [] []) =
      tapes c [] [] [] c.clause [] [] := by
    funext i; fin_cases i <;> simp [copyStacks, tapes]
  rw [hr, hs] at h
  exact .call _ h

def scopePorts : Fin 22 → Fin 31 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 30, 24, 19, 28]

theorem scopePorts_injective : Function.Injective scopePorts := by decide

abbrev makeScope : Cmd 11 31 := .call
  (ProgramLinking.liftProgram SubexpScopeProducer.program id scopePorts)

private theorem embed_scope (c : Inputs) (regs : Fin 11 → Bool)
    (source oldSource : List Bool) :
    embedState id scopePorts (data zeroRegs c [] [] [] oldSource [] [])
      (⟨regs, SubexpChunkRecordMap.tapes c.binaryEll source [] []⟩ : State 11 22) =
      data regs c [] [] [] source [] [] := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scopePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h24 : i ≠ 24 := fun h => hi ⟨19, by simpa [scopePorts] using h.symm⟩
    simp only [data, tapes, h24, ite_false]

theorem makeScope_eval (c : Inputs) (codes : List ℕ)
    (hell : 0 < BinaryArithmetic.toNat c.binaryEll)
    (hc : c.clause = Encoding.encodeList Encoding.encodeNat codes) :
    ∃ t ≤ SubexpScopeProducer.budget c.binaryEll codes + 1, ∃ rf,
      Eval makeScope t (data zeroRegs c [] [] [] c.clause [] [])
        (data rf c [] [] []
          (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope c.binaryEll codes)) [] []) := by
  obtain ⟨rf, t, ht, trace⟩ := SubexpScopeProducer.program_runsIn c.binaryEll codes hell
  have h := eval_call_lifted SubexpScopeProducer.program id scopePorts
    (data zeroRegs c [] [] [] c.clause [] [])
    Function.injective_id scopePorts_injective trace
  change Eval makeScope t
    (embedState id scopePorts (data zeroRegs c [] [] [] c.clause [] [])
      ⟨SubexpChunkRecordMap.regs false false false,
        SubexpChunkRecordMap.tapes c.binaryEll
          (Encoding.encodeList Encoding.encodeNat codes) [] []⟩)
    (embedState id scopePorts (data zeroRegs c [] [] [] c.clause [] [])
      ⟨rf, SubexpChunkRecordMap.tapes c.binaryEll
        (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope c.binaryEll codes)) [] []⟩) at h
  have hz : SubexpChunkRecordMap.regs false false false = zeroRegs := by
    funext i; fin_cases i <;> rfl
  rw [embed_scope, embed_scope, hz, ← hc] at h
  exact ⟨t, ht, rf, h⟩

def fieldMasters (c : Inputs) (rank arity scope fuel output : List Bool) :
    SubexpFieldRowProgram.Masters where
  modulus := c.modulus
  rank := rank
  arity := arity
  nShape := c.nShape
  fullShape := c.fullShape
  ell := c.ellShape
  scope := scope
  clause := c.clause
  width := c.widthShape
  fuel := fuel
  scratch := []
  output := output

def fieldRegisters : Fin 8 → Fin 11 := Fin.castAdd 3
def fieldPorts : Fin 30 → Fin 31 := Fin.castAdd 1

theorem fieldRegisters_injective : Function.Injective fieldRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
theorem fieldPorts_injective : Function.Injective fieldPorts := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 31 => x.val) h)

def extendRegs (outer : Fin 11 → Bool) (inner : Fin 8 → Bool) : Fin 11 → Bool :=
  fun i => if h : i.val < 8 then inner ⟨i.val, h⟩ else outer i

private theorem embed_field (c : Inputs) (outer : Fin 11 → Bool) (inner : Fin 8 → Bool)
    (rank oldRank arity scope fuel oldFuel output oldOutput : List Bool) :
    embedState fieldRegisters fieldPorts (data outer c [] oldRank arity scope oldFuel oldOutput)
      (SubexpFieldRowProgram.data inner (fieldMasters c rank arity scope fuel output)
        [] [] [] [] [] []) = data (extendRegs outer inner) c [] rank arity scope fuel output := by
  apply embedState_eq_of_ports _ _ _ _ _ fieldRegisters_injective fieldPorts_injective
  · intro i
    simp only [data, extendRegs, fieldRegisters, Fin.val_castAdd, i.isLt, dite_true]
    rfl
  · intro i hi
    have hge : ¬ i.val < 8 := by
      intro hlt
      exact hi ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    simp only [data, extendRegs, hge, dite_false]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h19 : i ≠ 19 := fun h => hi ⟨19, by simpa [fieldPorts] using h.symm⟩
    have h27 : i ≠ 27 := fun h => hi ⟨27, by simpa [fieldPorts] using h.symm⟩
    have h29 : i ≠ 29 := fun h => hi ⟨29, by simpa [fieldPorts] using h.symm⟩
    simp only [data, tapes, h19, h27, h29, ite_false]

abbrev makeTable : Cmd 11 31 := .call
  (ProgramLinking.liftProgram SubexpFieldTableEnumeration.program fieldRegisters fieldPorts)

/-- The lifted local table program still preserves the binary chunk width and
all higher caller registers. The final zero-valued fuel word is returned so
the caller can physically clear its full remaining width. -/
theorem makeTable_eval {D n : ℕ} (c : Inputs) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) (regs : Fin 11 → Bool) (arity fuel : List Bool)
    (hv : SubexpFieldTableEnumeration.Valid
      (fieldMasters c [] arity (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) fuel [])
      scope ls)
    (hfuel : CounterPrograms.value fuel = BinaryArithmetic.toNat c.modulus ^ scope.length) :
    let m := fieldMasters c [] arity
      (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) fuel []
    ∃ t ≤ SubexpEnumerationSchedule.programBudget SubexpFieldTableEnumeration.ports
        (fun _ => SubexpFieldTableEnumeration.callbackBound m scope ls
          (BinaryArithmetic.toNat c.modulus ^ scope.length))
        (SubexpFieldTableEnumeration.resting m (regs ∘ fieldRegisters) [] fuel []),
      ∃ rf rank remaining,
        Eval makeTable t
          (data regs c [] [] arity (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) fuel [])
          (data rf c [] rank arity (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) remaining
            (SubexpFieldTableEnumeration.rows m scope ls (BinaryArithmetic.toNat c.modulus ^ scope.length))) ∧
        rank.length ≤ BinaryArithmetic.toNat c.modulus ^ scope.length ∧
        remaining.length = fuel.length := by
  let m := fieldMasters c [] arity (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) fuel []
  obtain ⟨rf, rank, remaining, ⟨t, ht, trace⟩, _, _, hr, hf⟩ :=
    SubexpFieldTableEnumeration.table_runsIn m scope ls hv (regs ∘ fieldRegisters) fuel hfuel
  let frame := data regs c [] [] arity (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) fuel []
  have h := eval_call_lifted SubexpFieldTableEnumeration.program fieldRegisters fieldPorts frame
    fieldRegisters_injective fieldPorts_injective trace
  have hext : extendRegs regs (regs ∘ fieldRegisters) = regs := by
    funext i
    simp only [extendRegs]
    split
    · rfl
    · rfl
  simp only [SubexpFieldTableEnumeration.resting, SubexpFieldTableEnumeration.current,
    m, fieldMasters, List.append_nil] at h
  change Eval makeTable t
    (embedState fieldRegisters fieldPorts frame
      (SubexpFieldRowProgram.data (regs ∘ fieldRegisters) m [] [] [] [] [] []))
    (embedState fieldRegisters fieldPorts frame
      (SubexpFieldRowProgram.data rf
        (fieldMasters c rank arity (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) remaining
          (SubexpFieldTableEnumeration.rows m scope ls (BinaryArithmetic.toNat c.modulus ^ scope.length)))
        [] [] [] [] [] [])) at h
  dsimp only [frame, m] at h
  rw [embed_field, embed_field, hext] at h
  exact ⟨t, ht, _, rank, remaining, h, hr, hf⟩

@[simp] theorem tapes_clear_rank (c : Inputs) (exponent rank arity scope fuel output : List Bool) :
    clearStacks 19 (tapes c exponent rank arity scope fuel output) =
      tapes c exponent [] arity scope fuel output := by
  funext i; fin_cases i <;> simp [clearStacks, tapes]

@[simp] theorem tapes_clear_arity (c : Inputs) (exponent rank arity scope fuel output : List Bool) :
    clearStacks 20 (tapes c exponent rank arity scope fuel output) =
      tapes c exponent rank [] scope fuel output := by
  funext i; fin_cases i <;> simp [clearStacks, tapes]

@[simp] theorem tapes_clear_fuel (c : Inputs) (exponent rank arity scope fuel output : List Bool) :
    clearStacks 27 (tapes c exponent rank arity scope fuel output) =
      tapes c exponent rank arity scope [] output := by
  funext i; fin_cases i <;> simp [clearStacks, tapes]

@[simp] theorem tapes_clear_exponent (c : Inputs) (exponent rank arity scope fuel output : List Bool) :
    clearStacks 0 (tapes c exponent rank arity scope fuel output) =
      tapes c [] rank arity scope fuel output := by
  funext i; fin_cases i <;> simp [clearStacks, tapes]

private theorem clear_eval (port : Fin 31) (d : Data) :
    Eval (.call (clearProgram port (0 : Fin 11) 1)) (2 * (d.stacks port).length + 3)
      d ⟨readRegs d.regs 0 1 none, clearStacks port d.stacks⟩ := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace port (0 : Fin 11) 1 d.regs d.stacks) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc] using h

abbrev clearExponent : Cmd 11 31 := .call (clearProgram 0 0 1)

theorem clearExponent_eval (c : Inputs) (regs : Fin 11 → Bool)
    (exponent arity scope fuel : List Bool) :
    Eval clearExponent (2 * exponent.length + 3)
      (data regs c exponent [] arity scope fuel [])
      (data (readRegs regs 0 1 none) c [] [] arity scope fuel []) := by
  have h := clear_eval 0 (data regs c exponent [] arity scope fuel [])
  simpa [clearExponent, data, tapes_clear_exponent, tapes] using h

abbrev cleanup : Cmd 11 31 := .seq (.call (clearProgram 19 0 1))
  (.seq (.call (clearProgram 27 0 1)) (.seq (.call (clearProgram 20 0 1)) reset))

/-- Zero-valued padded counters are really consumed. Their full word widths
are charged in this cleanup, including the remaining fuel word. -/
theorem cleanup_eval (c : Inputs) (regs : Fin 11 → Bool)
    (rank arity scope fuel output : List Bool) :
    Eval cleanup (2 * rank.length + 2 * fuel.length + 2 * arity.length + 20)
      (data regs c [] rank arity scope fuel output)
      (data zeroRegs c [] [] [] scope [] output) := by
  let rr := readRegs regs 0 1 none
  have h₁ := clear_eval 19 (data regs c [] rank arity scope fuel output)
  have h₂ := clear_eval 27 (data rr c [] [] arity scope fuel output)
  have h₃ := clear_eval 20 (data rr c [] [] arity scope [] output)
  simp only [data, tapes_clear_rank] at h₁
  simp only [data, tapes_clear_fuel, rr, readRegs_reset] at h₂
  simp only [data, tapes_clear_arity, rr, readRegs_reset] at h₃
  have h₄ := reset_eval (data rr c [] [] [] scope [] output)
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  convert h using 1 <;> simp_all [tapes] <;> first | rfl | ring

def countPorts : Fin 15 → Fin 31 :=
  ![18, 24, 20, 0, 27, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem countPorts_injective : Function.Injective countPorts := by decide

def countInput (regs : Fin 11 → Bool) (c : Inputs) (scope : List Bool) :
    SubexpScopeCountSetup.Data :=
  ⟨regs ∘ fieldRegisters, fun i => if i = 0 then c.modulus else if i = 1 then scope else []⟩

private theorem countInput_project (regs : Fin 11 → Bool) (c : Inputs) (scope : List Bool) :
    countInput regs c scope =
      projectState fieldRegisters countPorts (data regs c [] [] [] scope [] []) := by
  apply state_ext
  · rfl
  · funext i; fin_cases i <;> rfl

private theorem embed_count_output (regs : Fin 11 → Bool) (c : Inputs) (scope : List Bool)
    (rf : Fin 8 → Bool) (arity : ℕ) (exponent fuel : List Bool) :
    embedState fieldRegisters countPorts (data regs c [] [] [] scope [] [])
      (⟨rf, SubexpScopeCountSetup.outputStacks (countInput regs c scope) arity exponent fuel⟩ :
        SubexpScopeCountSetup.Data) =
      data (extendRegs regs rf) c exponent [] (List.replicate arity true) scope fuel [] := by
  apply embedState_eq_of_ports _ _ _ _ _ fieldRegisters_injective countPorts_injective
  · intro i; simp only [data, extendRegs, fieldRegisters, Fin.val_castAdd, i.isLt, dite_true]
  · intro i hi
    have hge : ¬ i.val < 8 := by
      intro hlt
      exact hi ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    simp only [data, extendRegs, hge, dite_false]
  · intro i; fin_cases i <;> simp [data, tapes, SubexpScopeCountSetup.outputStacks,
      countInput, countPorts]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨3, by simpa [countPorts] using h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨2, by simpa [countPorts] using h.symm⟩
    have h27 : i ≠ 27 := fun h => hi ⟨4, by simpa [countPorts] using h.symm⟩
    simp only [data, tapes, h0, h20, h27, ite_false]

abbrev makeCount : Cmd 11 31 := .call
  (ProgramLinking.liftProgram SubexpScopeCountSetup.program fieldRegisters countPorts)

/-- The actual encoded scope determines the unary arity and binary p^arity
fuel. Only their representations, not their numeric values, are existential. -/
theorem makeCount_eval (c : Inputs) (regs : Fin 11 → Bool) (scope : List ℕ) :
    ∃ t ≤ SubexpScopeCountSetup.commandBound c.modulus.length
        (scope.map Encoding.encodeNat) + 1,
      ∃ rf exponent fuel,
        Eval makeCount t
          (data regs c [] [] [] (Encoding.encodeList Encoding.encodeNat scope) [] [])
          (data rf c exponent [] (List.replicate scope.length true)
            (Encoding.encodeList Encoding.encodeNat scope) fuel []) ∧
        BinaryArithmetic.toNat exponent = scope.length ∧ exponent.length ≤ scope.length ∧
        BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat c.modulus ^ scope.length ∧
        fuel.length ≤ 1 + scope.length * c.modulus.length := by
  let bits := Encoding.encodeList Encoding.encodeNat scope
  let d := countInput regs c bits
  have hready : SubexpScopeCountSetup.Ready d := by
    intro i h0 h1
    simp only [d, countInput, h0, h1, ite_false]
  have hscope : d.stacks 1 = Encoding.encodeList id (scope.map Encoding.encodeNat) := by
    exact (ExecLiteralDedupProgram.encode_nat_records scope).symm
  obtain ⟨rf, exponent, fuel, ⟨t, ht, trace⟩, he, hel, hf, hfl⟩ :=
    SubexpScopeCountSetup.program_runsIn (scope.map Encoding.encodeNat) d hscope hready
  have h := eval_call_lifted SubexpScopeCountSetup.program fieldRegisters countPorts
    (data regs c [] [] [] bits [] []) fieldRegisters_injective countPorts_injective trace
  change Eval makeCount t
    (embedState fieldRegisters countPorts (data regs c [] [] [] bits [] []) d)
    (embedState fieldRegisters countPorts (data regs c [] [] [] bits [] [])
      ⟨rf, SubexpScopeCountSetup.outputStacks d (scope.map Encoding.encodeNat).length exponent fuel⟩) at h
  dsimp only [d] at h
  have hi : embedState fieldRegisters countPorts (data regs c [] [] [] bits [] [])
      (countInput regs c bits) = data regs c [] [] [] bits [] [] := by
    rw [countInput_project]
    exact embedState_project fieldRegisters countPorts _ fieldRegisters_injective countPorts_injective
  rw [hi, embed_count_output] at h
  simp only [List.length_map] at h he hel hf hfl
  exact ⟨t, ht, _, exponent, fuel, h, he, hel, hf, hfl⟩

abbrev command : Cmd 11 31 := .seq reset (.seq copyClause (.seq makeScope
  (.seq makeCount (.seq clearExponent (.seq makeTable cleanup)))))

def program := compiled command (25 : Fin 31) 29

def tableMasters {D : ℕ} (c : Inputs) (scope : List (Fin D)) : SubexpFieldRowProgram.Masters :=
  fieldMasters c [] (List.replicate scope.length true)
    (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) [] []

def rowCount {D : ℕ} (c : Inputs) (scope : List (Fin D)) : ℕ :=
  BinaryArithmetic.toNat c.modulus ^ scope.length

def table {D n : ℕ} (c : Inputs) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) : List Bool :=
  SubexpFieldTableEnumeration.rows (tableMasters c scope) scope ls (rowCount c scope)

@[simp] theorem table_length {D n : ℕ} (c : Inputs) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) : (table c scope ls).length = rowCount c scope := by
  simp only [table, SubexpFieldTableEnumeration.rows, List.length_map,
    List.length_reverse, List.length_range]

def fuelWidth {D : ℕ} (c : Inputs) (scope : List (Fin D)) : ℕ :=
  1 + scope.length * c.modulus.length

def budget {D n : ℕ} (c : Inputs) (scope : List (Fin D))
    (ls : List (SAT.Literal (Fin n))) : ℕ :=
  11 + (7 * c.clause.length + 5) + (SubexpScopeProducer.budget c.binaryEll (codes ls) + 1) +
    (SubexpScopeCountSetup.commandBound c.modulus.length
      ((scope.map Fin.val).map Encoding.encodeNat) + 1) +
    (2 * scope.length + 3) +
    SubexpFieldTableEnumeration.enumerationBound (tableMasters c scope) scope ls
      (rowCount c scope) (fuelWidth c scope) +
    (2 * rowCount c scope + 2 * fuelWidth c scope + 2 * scope.length + 20)

/-- Complete physical construction from one canonical clause and preserved
parameter words. The scope and enumeration fuel are both produced by the
program. The only remaining hypotheses describe its input representation. -/
theorem command_eval {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) (regs : Fin 11 → Bool) :
    let scope := scopeOf c ls hv
    ∃ t ≤ budget c scope ls,
      Eval command t (data regs c [] [] [] [] [] [])
        (data zeroRegs c [] [] []
          (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) [] (table c scope ls)) := by
  let scope := scopeOf c ls hv
  let bits := Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)
  let arity := List.replicate scope.length true
  have hvalues : scope.map Fin.val = SubexpScopeProducer.scope c.binaryEll (codes ls) :=
    scopeOf_values c ls hv
  have hc : c.clause = Encoding.encodeList Encoding.encodeNat (codes ls) := hv.clause
  have hreset := reset_eval (data regs c [] [] [] [] [] [])
  have hcopy := copyClause_eval c
  obtain ⟨ns, hns, rs, hs⟩ := makeScope_eval c (codes ls) hv.ell_pos hc
  rw [← hvalues] at hs
  obtain ⟨nc, hnc, rc, exponent, fuel, hcount, hexp, hexpLen, hfuel, hfuelLen⟩ :=
    makeCount_eval c rs (scope.map Fin.val)
  simp only [List.length_map] at hcount hexp hexpLen hfuel hfuelLen
  have hclear := clearExponent_eval c rc exponent arity bits fuel
  let rr := readRegs rc 0 1 none
  let m := fieldMasters c [] arity bits fuel []
  have hm : SubexpFieldTableEnumeration.Valid m scope ls := by
    constructor
    · exact hv.modulus_pos
    · simp only [m, fieldMasters, arity, List.length_replicate]
    · exact hv.width
    · exact hv.ell_width
    · exact hv.full
    · exact hv.shape
    · exact hv.covered
    · rfl
    · exact hv.clause
  have hf : CounterPrograms.value fuel = BinaryArithmetic.toNat c.modulus ^ scope.length := by
    simpa only [CounterPrograms.value_eq_toNat] using hfuel
  obtain ⟨nt, hnt, rt, rank, remaining, htable, hrank, hremaining⟩ :=
    makeTable_eval c scope ls rr arity fuel hm hf
  have htableBound : nt ≤ SubexpFieldTableEnumeration.enumerationBound
      (tableMasters c scope) scope ls (rowCount c scope) (fuelWidth c scope) := by
    exact hnt.trans (SubexpFieldTableEnumeration.programBudget_le m scope ls
      (rr ∘ fieldRegisters) fuel [] (rowCount c scope) (fuelWidth c scope) hf hfuelLen)
  have hcleanup := cleanup_eval c rt rank arity bits remaining (table c scope ls)
  have hcleanupBound : 2 * rank.length + 2 * remaining.length + 2 * arity.length + 20 ≤
      2 * rowCount c scope + 2 * fuelWidth c scope + 2 * scope.length + 20 := by
    rw [hremaining]
    simp only [arity, List.length_replicate]
    change rank.length ≤ rowCount c scope at hrank
    change fuel.length ≤ fuelWidth c scope at hfuelLen
    omega
  have hclearBound : 2 * exponent.length + 3 ≤ 2 * scope.length + 3 := by omega
  have hrun := hreset.seq (hcopy.seq (hs.seq (hcount.seq (hclear.seq (htable.seq hcleanup)))))
  refine ⟨_, ?_, hrun⟩
  unfold budget
  dsimp only [scope] at hnc htableBound hcleanupBound hclearBound ⊢
  omega

theorem program_runsIn {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) (regs : Fin 11 → Bool) :
    let scope := scopeOf c ls hv
    RunsIn program (budget c scope ls + 1)
      ((data regs c [] [] [] [] [] []).withPC (some program.entry))
      ((data zeroRegs c [] [] []
        (Encoding.encodeList Encoding.encodeNat (scope.map Fin.val)) [] (table c scope ls)).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval c ls hv regs
  exact ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 25 29⟩

/-- The raw scope bytes are independent of the finite-index bound proof. -/
theorem program_runsIn_raw {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) (regs : Fin 11 → Bool) :
    RunsIn program (budget c (scopeOf c ls hv) ls + 1)
      ((data regs c [] [] [] [] [] []).withPC (some program.entry))
      ((data zeroRegs c [] [] [] (scopeBytes c ls) []
        (table c (scopeOf c ls hv) ls)).withPC none) := by
  simpa only [scopeOf_values, scopeBytes, rawScope] using program_runsIn c ls hv regs

theorem primitive_execution {D n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n)))
    (hv : Valid c D ls) (regs : Fin 11 → Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (budget c (scopeOf c ls hv) ls + 1))
      (primitiveCfg program ((data regs c [] [] [] [] [] []).withPC (some program.entry)))
      (primitiveCfg program ((data zeroRegs c [] [] [] (scopeBytes c ls) []
        (table c (scopeOf c ls hv) ls)).withPC none)) :=
  BitProgram.primitive_execution program (program_runsIn_raw c ls hv regs)

end SubexponentialSAT.SubexpClauseFactorProgram

end OAI.Algorithms
