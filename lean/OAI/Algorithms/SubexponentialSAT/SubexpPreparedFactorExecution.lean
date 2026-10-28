import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedFactorServices

namespace OAI.Algorithms

/-! Exact nested traversal of scalar lists, coordinate records, and rows. -/

namespace SubexponentialSAT.SubexpPreparedFactor

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

@[simp] theorem bufferPort_zero : bufferPort 0 = 15 := rfl
@[simp] theorem bufferPort_one : bufferPort 1 = 16 := rfl
@[simp] theorem bufferPort_two : bufferPort 2 = 17 := rfl

def recordsBody {α : Type*} (enc : α → Word) (xs : List α) : Word :=
  (xs.map (fun x => record (enc x))).flatten

theorem encodeList_eq {α : Type*} (enc : α → Word) (xs : List α) :
    Encoding.encodeList enc xs = recordsBody enc xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList,recordsBody,record,ih,List.append_assoc]

theorem emit_append (i : Fin 3) (x y : Word) (a : Buffers) :
    emit i y (emit i x a) = emit i (x ++ y) a := by
  funext j
  by_cases hj : j = i <;>
    simp [emit,Function.update_apply,hj,List.reverse_append,List.append_assoc]

theorem emit_other (i j : Fin 3) (h : j ≠ i) (bits : Word) (a : Buffers) :
    emit i bits a j = a j := by simp [emit,h]

theorem fold_emit {α : Type*} (i : Fin 3) (enc : α → Word) (xs : List α) (a : Buffers) :
    xs.foldl (fun a x => emit i (enc x) a) a = emit i (xs.map enc).flatten a := by
  induction xs generalizing a with
  | nil => simp [emit]
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emit_append]

theorem closeUpdate_emit (i j : Fin 3) (bits : Word) (a : Buffers) (hi : a i = []) :
    closeUpdate i j (emit i bits a) = emit j (record (bits ++ [false])) a := by
  have hclear : Function.update (emit i bits a) i [] = a := by
    simp [emit,Function.update_idem,←hi,Function.update_eq_self]
  unfold closeUpdate
  rw [hclear]
  have hbits : (false :: emit i bits a i).reverse = bits ++ [false] := by
    simp [emit,hi]
  rw [hbits]

theorem popTag_eval (r : Fin 5 → Bool) (D : ℕ) (b : Bool) (rest : Word) (a : Buffers) :
    Eval popTag 1 (ready r D (b :: rest) a)
      (ready (readRegs r 0 1 (some b)) D rest a) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (r := 5) (s := 22) 0 0 1) (ready r D (b :: rest) a))
  have hf : (StructuredProgram.Atom.pop (r := 5) (s := 22) 0 0 1).eval
      (ready r D (b :: rest) a) = ready (readRegs r 0 1 (some b)) D rest a := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [StructuredProgram.Atom.instr, execInstr, ready, work, stores]
    · funext j
      by_cases hj : j = 0 <;>
        simp [StructuredProgram.Atom.instr, execInstr, ready, work, stores, hj]
  rw [hf] at h
  exact h

def scanCost {α : Type*} (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => cost x + 2)).sum

def afterTag {α : Type*} (enc : α → Word) (xs : List α) (r : Fin 5 → Bool)
    (D : ℕ) (rest : Word) (a : Buffers) : Data :=
  match xs with
  | [] => ready (readRegs r 0 1 (some false)) D rest a
  | x :: xs => ready (readRegs r 0 1 (some true)) D
      (Encoding.frame (enc x) ++ (Encoding.encodeList enc xs ++ rest)) a

theorem popList_eval {α : Type*} (enc : α → Word) (xs : List α) (r : Fin 5 → Bool)
    (D : ℕ) (rest : Word) (a : Buffers) :
    Eval popTag 1 (ready r D (Encoding.encodeList enc xs ++ rest) a)
      (afterTag enc xs r D rest a) := by
  cases xs with
  | nil => simpa [afterTag,Encoding.encodeList] using popTag_eval r D false rest a
  | cons x xs =>
      simpa [afterTag,Encoding.encodeList,List.append_assoc] using
        popTag_eval r D true (Encoding.frame (enc x) ++ (Encoding.encodeList enc xs ++ rest)) a

theorem scanLoop_eval {α : Type*} (body : Code) (enc : α → Word) (cost : α → ℕ)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop) (D : ℕ)
    (hbody : ∀ x r rest a, inv a → ∃ r', Eval body (cost x)
      (ready r D (Encoding.frame (enc x) ++ rest) a) (ready r' D rest (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (r : Fin 5 → Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ r', Eval (.while 0 (.seq body popTag)) (1 + scanCost cost xs)
      (afterTag enc xs r D rest a)
      (ready r' D rest (xs.foldl (fun a x => update x a) a)) := by
  induction xs generalizing r a with
  | nil =>
      refine ⟨readRegs r 0 1 (some false),?_⟩
      apply Eval.while_false
      simp [afterTag,ready,work,readRegs]
  | cons x xs ih =>
      let tail := Encoding.encodeList enc xs ++ rest
      obtain ⟨r1,h1⟩ := hbody x (readRegs r 0 1 (some true)) tail a ha
      have h2 := popList_eval enc xs r1 D rest (update x a)
      obtain ⟨r2,h3⟩ := ih r1 (update x a) (hpreserve x a ha)
      have hguard : (afterTag enc (x :: xs) r D rest a).regs 0 = true := by
        simp [afterTag,ready,work,readRegs]
      have h := Eval.while_true hguard (h1.seq h2) h3
      refine ⟨r2,?_⟩
      have hcost : (cost x + 1) + (1 + scanCost cost xs) + 1 =
          1 + scanCost cost (x :: xs) := by
        simp only [scanCost, List.map_cons, List.sum_cons]
        omega
      rw [hcost] at h
      exact h

theorem scanBare_eval {α : Type*} (body : Code) (enc : α → Word) (cost : α → ℕ)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop) (D : ℕ)
    (hbody : ∀ x r rest a, inv a → ∃ r', Eval body (cost x)
      (ready r D (Encoding.frame (enc x) ++ rest) a) (ready r' D rest (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (r : Fin 5 → Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ r', Eval (scanBare body) (2 + scanCost cost xs)
      (ready r D (Encoding.encodeList enc xs ++ rest) a)
      (ready r' D rest (xs.foldl (fun a x => update x a) a)) := by
  have h1 := popList_eval enc xs r D rest a
  obtain ⟨r',h2⟩ := scanLoop_eval body enc cost update inv D hbody hpreserve xs r rest a ha
  refine ⟨r',?_⟩
  have h := h1.seq h2
  have hcost : 1 + (1 + scanCost cost xs) = 2 + scanCost cost xs := by
    omega
  rw [hcost] at h
  simpa only [scanBare] using h

theorem scan_eval {α : Type*} (body : Code) (enc : α → Word) (cost : α → ℕ)
    (update : α → Buffers → Buffers) (inv : Buffers → Prop) (D : ℕ)
    (hbody : ∀ x r rest a, inv a → ∃ r', Eval body (cost x)
      (ready r D (enc x ++ rest) a) (ready r' D rest (update x a)))
    (hpreserve : ∀ x a, inv a → inv (update x a))
    (xs : List α) (r : Fin 5 → Bool) (rest : Word) (a : Buffers) (ha : inv a) :
    ∃ r', Eval (scan body) (2 + scanCost (fun x => 9 * (enc x).length + 7 + cost x) xs)
      (ready r D (Encoding.encodeList enc xs ++ rest) a)
      (ready r' D rest (xs.foldl (fun a x => update x a) a)) := by
  apply scanBare_eval (.seq unframe body) enc (fun x => 9 * (enc x).length + 7 + cost x)
    update inv D ?_ hpreserve xs r rest a ha
  intro x r rest a ha
  have h1 := unframe_eval r D (enc x) rest a
  obtain ⟨r',h2⟩ := hbody x (readRegs r 0 1 none) rest a ha
  exact ⟨r',h1.seq h2⟩

def coordinatePrefix (D : ℕ) (c : Coordinate) : Word :=
  Encoding.frame c.input ++ recordsBody (SubexpScalarLiteralProgram.rawLiteral D) c.coefficients

def coordinateUpdate (D : ℕ) (c : Coordinate) (a : Buffers) : Buffers :=
  emit 1 (record (SubexpTableSource.encodeCoordinate (prepareCoordinate D c))) a

def coordinateCost (D : ℕ) (c : Coordinate) : ℕ :=
  7 * c.input.length + 5 + ((2 + scanCost (scalarCost D true) c.coefficients) +
    (13 * ((coordinatePrefix D c).length + 1) + 18))

theorem coordinateBody_eval (D : ℕ) (c : Coordinate) (r : Fin 5 → Bool)
    (rest : Word) (a : Buffers) (ha : a 0 = []) :
    ∃ r', Eval coordinateBody (coordinateCost D c)
      (ready r D (SubexpTableSource.encodeCoordinate c ++ rest) a)
      (ready r' D rest (coordinateUpdate D c a)) := by
  let tail := Encoding.encodeList id c.coefficients ++ rest
  let a0 := emit 0 (Encoding.frame c.input) a
  have h1 := captureFrame_eval 0 r D c.input tail a
  obtain ⟨r2,h2⟩ := scanBare_eval (emitScalar 15 true) id (scalarCost D true)
    (fun b a => emit 0 (record (SubexpScalarLiteralProgram.rawLiteral D b)) a)
    (fun _ => True) D
    (fun b r rest a _ => emitScalar_eval true 0 r D b rest a)
    (by intros; trivial) c.coefficients (readRegs r 0 1 (some false)) rest a0 trivial
  have h2' : Eval (scanBare (emitScalar 15 true))
      (2 + scanCost (scalarCost D true) c.coefficients)
      (ready (readRegs r 0 1 (some false)) D tail a0)
      (ready r2 D rest (emit 0 (coordinatePrefix D c) a)) := by
    simpa only [fold_emit,recordsBody,emit_append,coordinatePrefix,a0,tail] using h2
  obtain ⟨r3,h3⟩ := closeInto_eval 0 1 r2 D rest (emit 0 (coordinatePrefix D c) a)
  have hlen : ((emit 0 (coordinatePrefix D c) a) 0).length = (coordinatePrefix D c).length := by
    simp [emit,ha]
  have hbytes : coordinatePrefix D c ++ [false] =
      SubexpTableSource.encodeCoordinate (prepareCoordinate D c) := by
    simp [coordinatePrefix,SubexpTableSource.encodeCoordinate,prepareCoordinate,
      encodeList_eq,recordsBody,List.map_map,Function.comp_def,List.append_assoc]
  rw [hlen,closeUpdate_emit 0 1 _ a ha,hbytes] at h3
  refine ⟨r3,?_⟩
  simpa only [coordinateBody, bufferPort_zero, bufferPort_one, coordinateCost,
    SubexpTableSource.encodeCoordinate, List.append_assoc, coordinateUpdate, tail, a0] using
    h1.seq (h2'.seq h3)

def rowPrefix (D : ℕ) (row : Row) : Word :=
  Encoding.frame (SubexpScalarLiteralProgram.rawLiteral D row.value) ++
    recordsBody (fun c => SubexpTableSource.encodeCoordinate (prepareCoordinate D c)) row.coordinates

def rowUpdate (D : ℕ) (row : Row) (a : Buffers) : Buffers :=
  emit 2 (record (SubexpTableSource.encodeRow (prepareRow D row))) a

def rowCost (D : ℕ) (row : Row) : ℕ :=
  scalarCost D false row.value +
    ((2 + scanCost (fun c => 9 * (SubexpTableSource.encodeCoordinate c).length + 7 +
      coordinateCost D c) row.coordinates) + (13 * ((rowPrefix D row).length + 1) + 18))

theorem rowBody_eval (D : ℕ) (row : Row) (r : Fin 5 → Bool)
    (rest : Word) (a : Buffers) (h0 : a 0 = []) (h1 : a 1 = []) :
    ∃ r', Eval rowBody (rowCost D row)
      (ready r D (SubexpTableSource.encodeRow row ++ rest) a)
      (ready r' D rest (rowUpdate D row a)) := by
  let tail := Encoding.encodeList SubexpTableSource.encodeCoordinate row.coordinates ++ rest
  let a0 := emit 1 (Encoding.frame (SubexpScalarLiteralProgram.rawLiteral D row.value)) a
  obtain ⟨r1,e1⟩ := emitScalar_eval false 1 r D row.value tail a
  have ha0 : a0 0 = [] := by simp [a0,emit,h0]
  obtain ⟨r2,e2⟩ := scan_eval coordinateBody SubexpTableSource.encodeCoordinate
    (coordinateCost D) (coordinateUpdate D) (fun a => a 0 = []) D
    (fun c r rest a ha => coordinateBody_eval D c r rest a ha)
    (by intro c a ha; simpa [coordinateUpdate,emit] using ha)
    row.coordinates r1 rest a0 ha0
  have e2' : Eval (scan coordinateBody)
      (2 + scanCost (fun c => 9 * (SubexpTableSource.encodeCoordinate c).length + 7 +
        coordinateCost D c) row.coordinates)
      (ready r1 D tail a0) (ready r2 D rest (emit 1 (rowPrefix D row) a)) := by
    simpa only [coordinateUpdate,fold_emit,recordsBody,emit_append,rowPrefix,a0,tail] using e2
  obtain ⟨r3,e3⟩ := closeInto_eval 1 2 r2 D rest (emit 1 (rowPrefix D row) a)
  have hlen : ((emit 1 (rowPrefix D row) a) 1).length = (rowPrefix D row).length := by
    simp [emit,h1]
  have hbytes : rowPrefix D row ++ [false] = SubexpTableSource.encodeRow (prepareRow D row) := by
    simp [rowPrefix,SubexpTableSource.encodeRow,prepareRow,encodeList_eq,recordsBody,
      List.map_map,Function.comp_def,List.append_assoc]
  rw [hlen,closeUpdate_emit 1 2 _ a h1,hbytes] at e3
  refine ⟨r3,?_⟩
  simpa only [rowBody, bufferPort_one, bufferPort_two, rowCost,
    SubexpTableSource.encodeRow, List.append_assoc, rowUpdate, tail, a0, framed] using
    e1.seq (e2'.seq e3)

def tablePrefix (D : ℕ) (rows : List Row) : Word :=
  recordsBody (fun row => SubexpTableSource.encodeRow (prepareRow D row)) rows

def rowsCost (D : ℕ) (rows : List Row) : ℕ :=
  2 + scanCost (fun row => 9 * (SubexpTableSource.encodeRow row).length + 7 + rowCost D row) rows

theorem rows_eval (D : ℕ) (rows : List Row) (r : Fin 5 → Bool) (rest : Word)
    (a : Buffers) (h0 : a 0 = []) (h1 : a 1 = []) :
    ∃ r', Eval (scan rowBody) (rowsCost D rows)
      (ready r D (SubexpTableSource.encodeRows rows ++ rest) a)
      (ready r' D rest (emit 2 (tablePrefix D rows) a)) := by
  obtain ⟨r',h⟩ := scan_eval rowBody SubexpTableSource.encodeRow (rowCost D)
    (rowUpdate D) (fun a => a 0 = [] ∧ a 1 = []) D
    (fun row r rest a ha => rowBody_eval D row r rest a ha.1 ha.2)
    (by intro row a ha; simpa [rowUpdate,emit] using ha)
    rows r rest a ⟨h0,h1⟩
  refine ⟨r',?_⟩
  simpa only [SubexpTableSource.encodeRows,rowsCost,rowUpdate,fold_emit,tablePrefix,recordsBody] using h

theorem tablePrefix_eq (D : ℕ) (rows : List Row) :
    tablePrefix D rows ++ [false] = SubexpTableSource.encodeRows (prepareRows D rows) := by
  simp [SubexpTableSource.encodeRows,prepareRows,encodeList_eq,tablePrefix,recordsBody,
    List.map_map,Function.comp_def]

def runCost (D : ℕ) (rows : List Row) : ℕ :=
  rowsCost D rows + (2 + ((3 * (SubexpTableSource.encodeRows (prepareRows D rows)).length + 3) + 5)) + 1

theorem command_eval (D : ℕ) (rows : List Row) :
    Eval command (runCost D rows - 1)
      (serviceState D (SubexpTableSource.encodeRows rows))
      (serviceState D (SubexpTableSource.encodeRows (prepareRows D rows))) := by
  obtain ⟨r1,h1⟩ := rows_eval D rows (fun _ => false) [] emptyBuffers rfl rfl
  simp only [List.append_nil] at h1
  let a1 := emit 2 (tablePrefix D rows) emptyBuffers
  let a2 := Function.update a1 2 (false :: a1 2)
  have h2 := pushBuffer_eval 2 false r1 D [] a1
  have h3 := transfer_eval 17 0 (by decide)
    (ready (Function.update r1 0 false) D [] a2)
  have hbits : (a2 2).reverse = SubexpTableSource.encodeRows (prepareRows D rows) := by
    simp only [a2,Function.update_same,a1,emit,emptyBuffers,Function.update_same,
      List.append_nil,List.reverse_cons,List.reverse_reverse,tablePrefix_eq]
  have hlen : ((ready (Function.update r1 0 false) D [] a2).stacks 17).length =
      (SubexpTableSource.encodeRows (prepareRows D rows)).length := by
    rw [←hbits]
    simp [ready,work,stores]
  let r2 := readRegs (Function.update r1 0 false) 0 1 none
  have hfinal : afterTransfer 17 0 (ready (Function.update r1 0 false) D [] a2) =
      ready r2 D (SubexpTableSource.encodeRows (prepareRows D rows)) emptyBuffers := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases h0 : j = 0 <;> by_cases h17 : j = 17 <;>
        simp [ready, work, stores, StackRoutines.transferStacks, h0, h17, a2, a1,
          emit, emptyBuffers, tablePrefix_eq]
  rw [hlen,hfinal] at h3
  have h4 := reset_eval (ready r2 D (SubexpTableSource.encodeRows (prepareRows D rows)) emptyBuffers)
  simpa only [command, bufferPort_two, runCost, Nat.add_sub_cancel, serviceState, a1, a2,
    ready, work] using
    h1.seq (h2.seq (h3.seq h4))

/-- Every scalar singleton and every surrounding record frame is generated
by the fixed program. The Ce payload bytes are preserved exactly. -/
theorem program_trace (D : ℕ) (rows : List Row) :
    Trace program (runCost D rows)
      ((serviceState D (SubexpTableSource.encodeRows rows)).withPC (some program.entry))
      ((serviceState D (SubexpTableSource.encodeRows (prepareRows D rows))).withPC none) := by
  have h := compiled_halt_trace (command_eval D rows) 0 0
  simpa only [program, runCost, Nat.add_sub_cancel] using h

theorem primitive_execution (D : ℕ) (rows : List Row) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * runCost D rows)
      (BitProgram.primitiveCfg program
        ((serviceState D (SubexpTableSource.encodeRows rows)).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((serviceState D (SubexpTableSource.encodeRows (prepareRows D rows))).withPC none)) :=
  BitProgram.primitive_trace program (program_trace D rows)

end SubexponentialSAT.SubexpPreparedFactor

end OAI.Algorithms
