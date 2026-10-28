import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTableSource

namespace OAI.Algorithms

/-! Exact execution of the prepared-table source constructor. -/

namespace SubexponentialSAT.SubexpTableSource

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  setCounter counterWord)

local infixr:60 " ;; " => Cmd.seq

private def parserData (v p : Bool) (input output : Word) : State 2 2 :=
  ⟨ParserProgram.pair v p, ParserProgram.pair input output⟩

private theorem work_stacks_eq (v p c : Bool)
    (input zero one : Word) (a : Accumulator)
    (scratch ce code acc count : Word) :
    (work v p c input zero one a scratch ce code acc count).stacks =
      fun i => if i = 0 then input else if i = 1 then zero else
        if i = 2 then one else if i = 3 then a.output else
        if i = 4 then scratch else if i = 5 then a.outer else
        if i = 6 then a.groups else if i = 7 then ce else
        if i = 8 then code else if i = 9 then acc else
        if i = 10 then count else [] := by
  funext i
  fin_cases i <;> rfl

theorem parserRegs_injective : Function.Injective parserRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 3 => x.val) h)

theorem parserStacks_injective : Function.Injective parserStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [parserStacks, ParserProgram.pair]

theorem hornerPorts_injective : Function.Injective hornerPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [hornerPorts]

private theorem embed_capture (v p v' p' : Bool) (input input' zero one scratch : Word)
    (a : Accumulator) :
    embedState parserRegs parserStacks (state v p input zero one a)
      (parserData v' p' input' scratch) =
      work v' p' true input' zero one a scratch a.terms [] [] [] := by
  apply embedState_eq_of_ports
  · exact parserRegs_injective
  · exact parserStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact (hi ⟨0, rfl⟩).elim
    · exact (hi ⟨1, rfl⟩).elim
    · rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h4 : i ≠ 4 := fun h => hi ⟨1, h.symm⟩
    change (work v' p' true input' zero one a scratch a.terms [] [] []).stacks i =
      (work v p true input zero one a [] a.terms [] [] []).stacks i
    simp only [work_stacks_eq, h0, h4, ite_false]

theorem captureInput_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval captureInput (6 * bits.length + 4)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (work false true true rest zero one a bits.reverse a.terms [] [] []) := by
  have ht := ParserProgram.frame_trace bits rest [] v p
  simp only [List.append_nil] at ht
  have h := eval_call_lifted ParserProgram.frameProgram parserRegs parserStacks
    (state v p (Encoding.frame bits ++ rest) zero one a)
    parserRegs_injective parserStacks_injective
    (a := parserData v p (Encoding.frame bits ++ rest) [])
    (b := parserData false true rest bits.reverse) ht
  have hstate :
      work v p true (Encoding.frame bits ++ rest) zero one a [] a.terms [] [] [] =
        state v p (Encoding.frame bits ++ rest) zero one a := by
    rfl
  simpa only [captureInput, embed_capture, hstate] using h

def transferred (src dst : Fin 11) (d : State 3 11) : State 3 11 :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 11) (h : src ≠ dst) (d : State 3 11) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run src dst 0 1 h (by decide) d.regs d.stacks

def cleared (src : Fin 11) (d : State 3 11) : State 3 11 :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 11) (d : State 3 11) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src 0 1 d.regs d.stacks

theorem transferInput_eval (v p : Bool) (input zero one bits : Word) (a : Accumulator) :
    Eval (transfer 4 7) (3 * bits.length + 3)
      (work v p true input zero one a bits.reverse [] [] [] [])
      (work false false true input zero one a [] bits [] [] []) := by
  have he : transferred 4 7 (work v p true input zero one a bits.reverse [] [] [] []) =
      work false false true input zero one a [] bits [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [work, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;>
        simp [work, StackRoutines.transferStacks]
  have h := transfer_eval 4 7 (by decide)
    (work v p true input zero one a bits.reverse [] [] [] [])
  rw [he] at h
  have hlen : ((work v p true input zero one a bits.reverse [] [] [] []).stacks 4).length =
      bits.length := by simp [work]
  simpa only [hlen] using h

private def hornerData (v p c : Bool) (input x zero acc scratch count output : Word) : State 3 7 :=
  ⟨SubexpHornerProgram.triple v p c,
    SubexpHornerSource.seven input x zero acc scratch count output⟩

private theorem embed_horner (v p c v' p' c' : Bool)
    (input zero one scratch ce code acc count input' zero' scratch' ce' code' acc' count' : Word)
    (a : Accumulator) :
    embedState id hornerPorts (work v p c input zero one a scratch ce code acc count)
      (hornerData v' p' c' input' ce' zero' acc' scratch' count' code') =
      work v' p' c' input' zero' one a scratch' ce' code' acc' count' := by
  apply embedState_eq_of_ports
  · exact Function.injective_id
  · exact hornerPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨2, h.symm⟩
    have h4 : i ≠ 4 := fun h => hi ⟨4, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨1, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨6, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨5, h.symm⟩
    simp only [work_stacks_eq, h0, h1, h4, h7, h8, h9, h10, ite_false]

theorem horner_eval (cs : List Word) (rest x zero one : Word) (a : Accumulator) :
    Eval horner (SubexpHornerSource.runCost x zero cs)
      (work false false true (Encoding.encodeList id cs ++ rest) zero one a [] x [] [] [])
      (work false false false rest zero one a [] x
        (SubexpHornerSource.source x zero cs) [] []) := by
  have ht := SubexpHornerSource.trace cs rest x zero [] false false true
  simp only [List.append_nil] at ht
  have h := eval_call_lifted SubexpHornerSource.program id hornerPorts
    (work false false true (Encoding.encodeList id cs ++ rest) zero one a [] x [] [] [])
    Function.injective_id hornerPorts_injective
    (a := hornerData false false true (Encoding.encodeList id cs ++ rest) x zero [] [] [] [])
    (b := hornerData false false false rest x zero [] [] [] (SubexpHornerSource.source x zero cs)) ht
  simpa only [horner, embed_horner] using h

theorem appendHorner_eval (input zero one x code : Word) (a : Accumulator) :
    Eval (transfer 8 3) (3 * code.length + 3)
      (work false false false input zero one a [] x code [] [])
      (work false false false input zero one (emit code a) [] x [] [] []) := by
  have he : transferred 8 3 (work false false false input zero one a [] x code [] []) =
      work false false false input zero one (emit code a) [] x [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [work, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;>
        simp [work, StackRoutines.transferStacks, emit]
  have h := transfer_eval 8 3 (by decide)
    (work false false false input zero one a [] x code [] [])
  have hlen : ((work false false false input zero one a [] x code [] []).stacks 8).length =
      code.length := by
    rfl
  simpa only [he, hlen] using h

theorem clearInput_eval (input zero one x : Word) (a : Accumulator) :
    Eval (clear 7) (2 * x.length + 3)
      (work false false false input zero one a [] x [] [] [])
      (work false false false input zero one a [] [] [] [] []) := by
  have he : cleared 7 (work false false false input zero one a [] x [] [] []) =
      work false false false input zero one a [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [work, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;>
        simp [work, StackRoutines.clearStacks]
  have h := clear_eval 7 (work false false false input zero one a [] x [] [] [])
  have hlen : ((work false false false input zero one a [] x [] [] []).stacks 7).length =
      x.length := by
    rfl
  simpa only [he, hlen] using h

abbrev setConstant (b : Bool) : Cmd 3 11 := .base (.atom (.set 2 b))

theorem setConstant_eval (v p c b : Bool) (input zero one : Word) (a : Accumulator)
    (scratch ce code acc count : Word) :
    Eval (setConstant b) 1 (work v p c input zero one a scratch ce code acc count)
      (work v p b input zero one a scratch ce code acc count) := by
  have he : (StructuredProgram.Atom.set (s := 11) (2 : Fin 3) b).eval
      (work v p c input zero one a scratch ce code acc count) =
      work v p b input zero one a scratch ce code acc count := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [StructuredProgram.Atom.instr, execInstr, work, SubexpHornerProgram.triple]
    · rfl
  rw [← he]
  exact .base (.atom _ _)

def coordinateUpdate (zero : Word) (c : Coordinate) (a : Accumulator) : Accumulator :=
  bump 1 (emit (coordinateCode zero c) a)

def coordinateCost (zero : Word) (c : Coordinate) : ℕ :=
  SubexpHornerSource.runCost c.input zero c.coefficients + 11 * c.input.length +
    3 * (coordinateCode zero c).length + 16

theorem coordinateBody_eval (c : Coordinate) (rest zero one : Word) (a : Accumulator)
    (ha : a.terms = []) :
    Eval coordinateBody (coordinateCost zero c)
      (state false false (encodeCoordinate c ++ rest) zero one a)
      (state false false rest zero one (coordinateUpdate zero c a)) := by
  let tail := Encoding.encodeList id c.coefficients ++ rest
  have h₁ := captureInput_eval false false c.input tail zero one a
  simp only [ha] at h₁
  have h₂ := transferInput_eval false true tail zero one c.input a
  have h₃ := horner_eval c.coefficients rest c.input zero one a
  have h₄ := appendHorner_eval rest zero one c.input (coordinateCode zero c) a
  have h₅ := clearInput_eval rest zero one c.input (emit (coordinateCode zero c) a)
  have h₆ := setConstant_eval false false false true rest zero one
    (emit (coordinateCode zero c) a) [] [] [] [] []
  have h₇ := countOne_eval 1 false false rest zero one (emit (coordinateCode zero c) a)
  have hclean : (emit (coordinateCode zero c) a).terms = [] := ha
  simp only [state, hclean] at h₇
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄
    (Eval.seq h₅ (Eval.seq h₆ h₇)))))
  convert h using 1 <;>
    (try simp [coordinateCost, coordinateCode, coordinateUpdate,
      encodeCoordinate, tail, List.append_assoc, state])
  all_goals omega

/-! ## The two actual record-traversal loops -/

def scanCost {α : Type*} (encode : α → Word) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => 9 * (encode x).length + cost x + 11)).sum

def afterTag {α : Type*} (encode : α → Word) (xs : List α) (rest zero one : Word)
    (a : Accumulator) : State 3 11 :=
  match xs with
  | [] => state false true rest zero one a
  | x :: xs => state true true
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest)) zero one a

theorem popList_eval {α : Type*} (encode : α → Word) (xs : List α)
    (v p : Bool) (rest zero one : Word) (a : Accumulator) :
    Eval popTag 2 (state v p (Encoding.encodeList encode xs ++ rest) zero one a)
      (afterTag encode xs rest zero one a) := by
  cases xs with
  | nil => simpa [afterTag, Encoding.encodeList] using popTag_eval false v p rest zero one a
  | cons x xs =>
      simpa [afterTag, Encoding.encodeList, List.append_assoc] using
        popTag_eval true v p (Encoding.frame (encode x) ++
          (Encoding.encodeList encode xs ++ rest)) zero one a

theorem scanLoop_eval {α : Type*} (body : Cmd 3 11) (encode : α → Word)
    (cost : α → ℕ) (update : α → Accumulator → Accumulator)
    (invariant : Accumulator → Prop) (zero one : Word) (vb pb : Bool)
    (hbody : ∀ x rest a, invariant a →
      Eval body (cost x) (state false false (encode x ++ rest) zero one a)
        (state vb pb rest zero one (update x a)))
    (hpreserve : ∀ x a, invariant a → invariant (update x a))
    (xs : List α) (rest : Word) (a : Accumulator) (ha : invariant a) :
    Eval (scanLoop body) (1 + scanCost encode cost xs)
      (afterTag encode xs rest zero one a)
      (state false true rest zero one (xs.foldl (fun a x => update x a) a)) := by
  induction xs generalizing a with
  | nil =>
      apply Eval.while_false
      simp [afterTag, state, work, SubexpHornerProgram.triple]
  | cons x xs ih =>
      let tail := Encoding.encodeList encode xs ++ rest
      have hread := unframe_eval true true (encode x) tail zero one a
      have hrun := hbody x tail a ha
      have hpop := popList_eval encode xs vb pb rest zero one (update x a)
      have hrest := ih (update x a) (hpreserve x a ha)
      have hguard : (afterTag encode (x :: xs) rest zero one a).regs 0 = true := by
        simp [afterTag, state, work, SubexpHornerProgram.triple]
      have h := Eval.while_true hguard (Eval.seq hread (Eval.seq hrun hpop)) hrest
      convert h using 1 <;>
        (try simp [scanCost, List.foldl_cons,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])
      all_goals omega

theorem scan_eval {α : Type*} (body : Cmd 3 11) (encode : α → Word)
    (cost : α → ℕ) (update : α → Accumulator → Accumulator)
    (invariant : Accumulator → Prop) (zero one : Word) (vb pb : Bool)
    (hbody : ∀ x rest a, invariant a →
      Eval body (cost x) (state false false (encode x ++ rest) zero one a)
        (state vb pb rest zero one (update x a)))
    (hpreserve : ∀ x a, invariant a → invariant (update x a))
    (xs : List α) (v p : Bool) (rest : Word) (a : Accumulator) (ha : invariant a) :
    Eval (scan body) (3 + scanCost encode cost xs)
      (state v p (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have hpop := popList_eval encode xs v p rest zero one a
  have hloop := scanLoop_eval body encode cost update invariant zero one vb pb
    hbody hpreserve xs rest a ha
  convert Eval.seq hpop hloop using 1
  all_goals omega

def rowUpdate (zero one : Word) (r : Row) (a : Accumulator) : Accumulator :=
  bump 0 (emit (rowCode zero one r) a)

def rowCost (zero one : Word) (r : Row) : ℕ :=
  7 * r.value.length + scanCost encodeCoordinate (coordinateCost zero) r.coordinates +
    8 * one.length + 4 * r.coordinates.length + 29

theorem rowBody_eval (r : Row) (rest zero one : Word) (a : Accumulator)
    (hg : a.groups = []) (ht : a.terms = []) :
    Eval rowBody (rowCost zero one r)
      (state false false (encodeRow r ++ rest) zero one a)
      (state false false rest zero one (rowUpdate zero one r a)) := by
  let tail := Encoding.encodeList encodeCoordinate r.coordinates ++ rest
  let a₀ := emit (pushWord r.value) a
  let pre := (r.coordinates.map (coordinateCode zero)).flatten
  let pending := List.replicate r.coordinates.length true
  have h₁ := emitFramedLiteral_eval false false r.value tail zero one a
  have ha₀g : a₀.groups = [] := hg
  have ha₀t : a₀.terms = [] := ht
  have hs := scan_eval coordinateBody encodeCoordinate (coordinateCost zero)
    (coordinateUpdate zero) (fun a => a.terms = []) zero one false false
    (fun c rest a ha => coordinateBody_eval c rest zero one a ha)
    (by intro c a ha; simpa [coordinateUpdate, bump, setCounter, emit] using ha)
    r.coordinates false true rest a₀ ha₀t
  have hs' : Eval (scan coordinateBody)
      (3 + scanCost encodeCoordinate (coordinateCost zero) r.coordinates)
      (state false true tail zero one a₀)
      (state false true rest zero one (emit pre (setCounter 1 pending a₀))) := by
    simpa [coordinateUpdate, SubexpKernelControl.fold_bump_emit, pre, pending,
      counterWord, ha₀g, tail] using hs
  have ho := emitLiteral_eval true false true rest zero one (emit pre (setCounter 1 pending a₀))
  have hd := drain_eval 1 true pending false false rest zero one
    (emit (pre ++ pushWord one) a₀)
  have hd' : Eval (drain 1 true) (4 * r.coordinates.length + 3)
      (state false false rest zero one
        (emit (pushWord one) (emit pre (setCounter 1 pending a₀))))
      (state false false rest zero one
        (emit (pre ++ pushWord one ++ operators true r.coordinates.length) a₀)) := by
    have hclear := SubexpKernelControl.setCounter_same (1 : Fin 3) a₀
    have hword : counterWord (1 : Fin 3) a₀ = [] := ha₀g
    rw [hword] at hclear
    simpa [pending, SubexpKernelControl.emit_emit, hclear, List.append_assoc] using hd
  have hm := emitOperator_eval true false false rest zero one
    (emit (pre ++ pushWord one ++ operators true r.coordinates.length) a₀)
  have hc := countOne_eval 0 false false rest zero one
    (emit (operator true) (emit (pre ++ pushWord one ++ operators true r.coordinates.length) a₀))
  have h := Eval.seq h₁ (Eval.seq hs' (Eval.seq ho (Eval.seq hd' (Eval.seq hm hc))))
  convert h using 1 <;>
    (try simp [rowCost, encodeRow, tail, rowUpdate, rowCode, a₀, pre,
      SubexpKernelControl.emit_emit, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
  all_goals omega

def tableCost (zero one : Word) (rs : List Row) : ℕ :=
  scanCost encodeRow (rowCost zero one) rs + 8 * zero.length + 5 * rs.length + 16

/-- Both body premises of the record induction are discharged by concrete
program traces above. The final theorem takes no callback premise. -/
theorem table_eval (rs : List Row) (v p : Bool) (rest zero one : Word) (a : Accumulator)
    (ho : a.outer = []) (hg : a.groups = []) (ht : a.terms = []) :
    Eval table (tableCost zero one rs)
      (state v p (encodeRows rs ++ rest) zero one a)
      (state false false rest zero one (emit (tableCode zero one rs) a)) := by
  let pre := (rs.map (rowCode zero one)).flatten
  let pending := List.replicate rs.length true
  have hs := scan_eval rowBody encodeRow (rowCost zero one) (rowUpdate zero one)
    (fun a => a.groups = [] ∧ a.terms = []) zero one false false
    (fun r rest a ha => rowBody_eval r rest zero one a ha.1 ha.2)
    (by intro r a ha; simpa [rowUpdate, bump, setCounter, emit] using ha)
    rs v p rest a ⟨hg, ht⟩
  have hs' : Eval (scan rowBody) (3 + scanCost encodeRow (rowCost zero one) rs)
      (state v p (encodeRows rs ++ rest) zero one a)
      (state false true rest zero one (emit pre (setCounter 0 pending a))) := by
    simpa [encodeRows, rowUpdate, SubexpKernelControl.fold_bump_emit, pre,
      pending, counterWord, ho] using hs
  have hz := emitLiteral_eval false false true rest zero one (emit pre (setCounter 0 pending a))
  have hd := drain_eval 0 false pending false false rest zero one (emit (pre ++ pushWord zero) a)
  have hd' : Eval (drain 0 false) (5 * rs.length + 3)
      (state false false rest zero one (emit (pushWord zero) (emit pre (setCounter 0 pending a))))
      (state false false rest zero one (emit (tableCode zero one rs) a)) := by
    have hclear := SubexpKernelControl.setCounter_same (0 : Fin 3) a
    have hword : counterWord (0 : Fin 3) a = [] := ho
    rw [hword] at hclear
    simpa [pending, tableCode, pre, SubexpKernelControl.emit_emit, hclear,
      List.append_assoc] using hd
  convert Eval.seq hs' (Eval.seq hz hd') using 1
  all_goals (try simp [tableCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
  all_goals omega

/-! ## Complete fixed program: input and output share port 0 -/

def emptyAccumulator : Accumulator := ⟨[], [], [], []⟩

def serviceState (input zero one : Word) : State 3 11 :=
  work false false false input zero one emptyAccumulator [] [] [] [] []

abbrev sourceConstructor : Cmd 3 11 :=
  setConstant true ;; table ;; transfer 3 0 ;; setConstant false

abbrev program : Program 3 11 (StructuredCalls.size sourceConstructor + 1) :=
  StructuredCalls.compiled sourceConstructor 0 0

theorem constructor_eval (zero one : Word) (rs : List Row) :
    Eval sourceConstructor (tableCost zero one rs + 3 * (tableCode zero one rs).length + 5)
      (serviceState (encodeRows rs) zero one)
      (serviceState (tableCode zero one rs) zero one) := by
  have henter := setConstant_eval false false false true (encodeRows rs) zero one
    emptyAccumulator [] [] [] [] []
  have ht := table_eval rs false false [] zero one emptyAccumulator rfl rfl rfl
  simp only [List.append_nil] at ht
  have he : transferred 3 0 (state false false [] zero one (emit (tableCode zero one rs) emptyAccumulator)) =
      state false false (tableCode zero one rs) zero one emptyAccumulator := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [state, work, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;>
        simp [state, work, StackRoutines.transferStacks, emit, emptyAccumulator]
  have hmove := transfer_eval 3 0 (by decide)
    (state false false [] zero one (emit (tableCode zero one rs) emptyAccumulator))
  have hmove' : Eval (transfer 3 0) (3 * (tableCode zero one rs).length + 3)
      (state false false [] zero one (emit (tableCode zero one rs) emptyAccumulator))
      (state false false (tableCode zero one rs) zero one emptyAccumulator) := by
    rw [he] at hmove
    have hlen : ((state false false [] zero one
        (emit (tableCode zero one rs) emptyAccumulator)).stacks 3).length =
        (tableCode zero one rs).length := by
      simp [state, work, emit, emptyAccumulator]
    simpa only [hlen] using hmove
  have hexit := setConstant_eval false false true false (tableCode zero one rs) zero one
    emptyAccumulator [] [] [] [] []
  have h := Eval.seq henter (Eval.seq ht (Eval.seq hmove' hexit))
  convert h using 1
  all_goals (try simp [serviceState, emptyAccumulator, Nat.add_assoc, Nat.add_comm])
  all_goals omega

/-- Actual row and coordinate traversal, including the case of an empty
table. Constants survive; every work port and Boolean register is cleared. -/
theorem program_trace (zero one : Word) (rs : List Row) :
    Trace program (tableCost zero one rs + 3 * (tableCode zero one rs).length + 6)
      ((serviceState (encodeRows rs) zero one).withPC (some program.entry))
      ((serviceState (tableCode zero one rs) zero one).withPC none) := by
  have h := StructuredCalls.compiled_halt_trace (constructor_eval zero one rs) 0 0
  simpa only [Nat.add_assoc] using h

theorem program_table_trace {R A : Type*} [Zero A] [One A] {p k : ℕ}
    (encode : A → Word) (literal : R → A) (cache : List (List R))
    (inputs : Fin k → A) (rows : List (SubexpTableInterpolation.Row p k R)) :
    Trace program
      (tableCost (encode 0) (encode 1) (rows.map (ofRow encode literal cache inputs)) +
        3 * (SubexpPostfixControl.serializeCode encode
          (SubexpTableInterpolation.tableExpr literal cache rows (fun i => .lit (inputs i))).compile).length + 6)
      ((serviceState (encodeRows (rows.map (ofRow encode literal cache inputs))) (encode 0) (encode 1)).withPC
        (some program.entry))
      ((serviceState (SubexpPostfixControl.serializeCode encode
        (SubexpTableInterpolation.tableExpr literal cache rows (fun i => .lit (inputs i))).compile)
          (encode 0) (encode 1)).withPC none) := by
  simpa only [tableCode_eq] using
    program_trace (encode 0) (encode 1) (rows.map (ofRow encode literal cache inputs))

theorem primitive_execution (zero one : Word) (rs : List Row) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (tableCost zero one rs + 3 * (tableCode zero one rs).length + 6))
      (BitProgram.primitiveCfg program
        ((serviceState (encodeRows rs) zero one).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((serviceState (tableCode zero one rs) zero one).withPC none)) :=
  BitProgram.primitive_trace program (program_trace zero one rs)

end SubexponentialSAT.SubexpTableSource

end OAI.Algorithms
