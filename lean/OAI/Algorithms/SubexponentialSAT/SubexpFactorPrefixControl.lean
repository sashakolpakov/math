import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketRows
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! Fixed control for grouping aligned incidence prefixes by physical scope
record counts. All list lengths are runtime data. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes prefixBytes)
open Subexp.FactorPacketRows (prefixStream)

abbrev Data := State 8 24

def groupBytes (ps : List Prefix) : Word :=
  Encoding.frame (List.replicate ps.length true) ++ Encoding.frame (prefixStream ps)

def scopeBytes (scope : List ℕ) : Word := Encoding.encodeList Encoding.encodeNat scope
def originStream (ps : List Prefix) : Word := Encoding.encodeList originBytes ps
def taylorStream (ps : List Prefix) : Word := Encoding.encodeList taylorBytes ps
def groupStream (groups : List (List Prefix)) : Word := Encoding.encodeList groupBytes groups

/-- The grouping used by the implementation: successive physical scope
lengths select successive prefixes, without sorting or removing duplicates. -/
def regroup : List ℕ → List Prefix → List (List Prefix)
  | [], _ => []
  | n :: ns, ps => ps.take n :: regroup ns (ps.drop n)

structure View where
  origins : Word := []
  taylor : Word := []
  scopes : Word := []
  output : Word := []
  todoTaylor : Word := []
  todoScopes : Word := []
  scope : Word := []
  arity : Word := []
  count : Word := []
  origin : Word := []
  column : Word := []
  prefixData : Word := []
  reversePrefixes : Word := []
  prefixes : Word := []
  group : Word := []
  reverseGroups : Word := []
  parseTmp : Word := []
  copyTmp : Word := []
  reverseTmp : Word := []

def store (v : View) : Fin 24 → Word := fun i =>
  if i = 0 then v.origins else if i = 1 then v.taylor else if i = 2 then v.scopes
  else if i = 3 then v.output else if i = 4 then v.todoTaylor else if i = 5 then v.todoScopes
  else if i = 6 then v.scope else if i = 7 then v.arity else if i = 8 then v.count
  else if i = 9 then v.origin else if i = 10 then v.column else if i = 11 then v.prefixData
  else if i = 12 then v.reversePrefixes else if i = 13 then v.prefixes else if i = 14 then v.group
  else if i = 15 then v.reverseGroups else if i = 16 then v.parseTmp else if i = 17 then v.copyTmp
  else if i = 18 then v.reverseTmp else []

def state (regs : Fin 8 → Bool) (v : View) : Data := ⟨regs, store v⟩

@[simp] theorem store_origins (v : View) : store v 0 = v.origins := rfl
@[simp] theorem update_origins (v : View) (w : Word) :
    Function.update (store v) 0 w = store {v with origins := w} := by
  funext j
  by_cases h : j = 0 <;> simp [store, h]

@[simp] theorem store_taylor (v : View) : store v 1 = v.taylor := rfl
@[simp] theorem update_taylor (v : View) (w : Word) :
    Function.update (store v) 1 w = store {v with taylor := w} := by
  funext j
  by_cases h : j = 1 <;> simp [store, h]

@[simp] theorem store_scopes (v : View) : store v 2 = v.scopes := rfl
@[simp] theorem update_scopes (v : View) (w : Word) :
    Function.update (store v) 2 w = store {v with scopes := w} := by
  funext j
  by_cases h : j = 2 <;> simp [store, h]

@[simp] theorem store_output (v : View) : store v 3 = v.output := rfl
@[simp] theorem update_output (v : View) (w : Word) :
    Function.update (store v) 3 w = store {v with output := w} := by
  funext j
  by_cases h : j = 3 <;> simp [store, h]

@[simp] theorem store_todoTaylor (v : View) : store v 4 = v.todoTaylor := rfl
@[simp] theorem update_todoTaylor (v : View) (w : Word) :
    Function.update (store v) 4 w = store {v with todoTaylor := w} := by
  funext j
  by_cases h : j = 4 <;> simp [store, h]

@[simp] theorem store_todoScopes (v : View) : store v 5 = v.todoScopes := rfl
@[simp] theorem update_todoScopes (v : View) (w : Word) :
    Function.update (store v) 5 w = store {v with todoScopes := w} := by
  funext j
  by_cases h : j = 5 <;> simp [store, h]

@[simp] theorem store_scope (v : View) : store v 6 = v.scope := rfl
@[simp] theorem update_scope (v : View) (w : Word) :
    Function.update (store v) 6 w = store {v with scope := w} := by
  funext j
  by_cases h : j = 6 <;> simp [store, h]

@[simp] theorem store_arity (v : View) : store v 7 = v.arity := rfl
@[simp] theorem update_arity (v : View) (w : Word) :
    Function.update (store v) 7 w = store {v with arity := w} := by
  funext j
  by_cases h : j = 7 <;> simp [store, h]

@[simp] theorem store_count (v : View) : store v 8 = v.count := rfl
@[simp] theorem update_count (v : View) (w : Word) :
    Function.update (store v) 8 w = store {v with count := w} := by
  funext j
  by_cases h : j = 8 <;> simp [store, h]

@[simp] theorem store_origin (v : View) : store v 9 = v.origin := rfl
@[simp] theorem update_origin (v : View) (w : Word) :
    Function.update (store v) 9 w = store {v with origin := w} := by
  funext j
  by_cases h : j = 9 <;> simp [store, h]

@[simp] theorem store_column (v : View) : store v 10 = v.column := rfl
@[simp] theorem update_column (v : View) (w : Word) :
    Function.update (store v) 10 w = store {v with column := w} := by
  funext j
  by_cases h : j = 10 <;> simp [store, h]

@[simp] theorem store_prefixData (v : View) : store v 11 = v.prefixData := rfl
@[simp] theorem update_prefixData (v : View) (w : Word) :
    Function.update (store v) 11 w = store {v with prefixData := w} := by
  funext j
  by_cases h : j = 11 <;> simp [store, h]

@[simp] theorem store_reversePrefixes (v : View) : store v 12 = v.reversePrefixes := rfl
@[simp] theorem update_reversePrefixes (v : View) (w : Word) :
    Function.update (store v) 12 w = store {v with reversePrefixes := w} := by
  funext j
  by_cases h : j = 12 <;> simp [store, h]

@[simp] theorem store_prefixes (v : View) : store v 13 = v.prefixes := rfl
@[simp] theorem update_prefixes (v : View) (w : Word) :
    Function.update (store v) 13 w = store {v with prefixes := w} := by
  funext j
  by_cases h : j = 13 <;> simp [store, h]

@[simp] theorem store_group (v : View) : store v 14 = v.group := rfl
@[simp] theorem update_group (v : View) (w : Word) :
    Function.update (store v) 14 w = store {v with group := w} := by
  funext j
  by_cases h : j = 14 <;> simp [store, h]

@[simp] theorem store_reverseGroups (v : View) : store v 15 = v.reverseGroups := rfl
@[simp] theorem update_reverseGroups (v : View) (w : Word) :
    Function.update (store v) 15 w = store {v with reverseGroups := w} := by
  funext j
  by_cases h : j = 15 <;> simp [store, h]

@[simp] theorem store_parseTmp (v : View) : store v 16 = v.parseTmp := rfl
@[simp] theorem update_parseTmp (v : View) (w : Word) :
    Function.update (store v) 16 w = store {v with parseTmp := w} := by
  funext j
  by_cases h : j = 16 <;> simp [store, h]

@[simp] theorem store_copyTmp (v : View) : store v 17 = v.copyTmp := rfl
@[simp] theorem update_copyTmp (v : View) (w : Word) :
    Function.update (store v) 17 w = store {v with copyTmp := w} := by
  funext j
  by_cases h : j = 17 <;> simp [store, h]

@[simp] theorem store_reverseTmp (v : View) : store v 18 = v.reverseTmp := rfl
@[simp] theorem update_reverseTmp (v : View) (w : Word) :
    Function.update (store v) 18 w = store {v with reverseTmp := w} := by
  funext j
  by_cases h : j = 18 <;> simp [store, h]


abbrev atom (a : StructuredProgram.Atom 8 24) : Cmd 8 24 := .base (.atom a)
abbrev push (dst : Fin 24) (b : Bool) : Cmd 8 24 := Subexp.TupleProgram.pushConst dst 0 b
abbrev clear (src : Fin 24) : Cmd 8 24 := .call (StackRoutines.clearProgram src 0 1)
abbrev copy (src dst : Fin 24) : Cmd 8 24 := Subexp.MatrixProgramSupport.copy src dst 17
abbrev readWord (src dst : Fin 24) (h : src ≠ 16) : Cmd 8 24 :=
  Subexp.MatrixProgramSupport.readWord src dst 16 h
abbrev emitFrame (src dst : Fin 24) (h : (16 : Fin 24) ≠ dst) : Cmd 8 24 :=
  Subexp.MatrixProgramSupport.emitFrame src dst 16 h
abbrev emitRecord (src dst : Fin 24) (h : (16 : Fin 24) ≠ dst) : Cmd 8 24 :=
  .seq (emitFrame src dst h) (push dst true)

def countRegisters (i : Fin 2) : Fin 8 := Fin.castAdd 6 i
def countStacks : Fin 2 → Fin 24 := ![6, 7]
theorem countRegisters_injective : Function.Injective countRegisters := Fin.castAdd_injective _ _
theorem countStacks_injective : Function.Injective countStacks := by decide
abbrev countScope : Cmd 8 24 := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram countRegisters countStacks)

def reverseRegisters (i : Fin 3) : Fin 8 := Fin.castAdd 5 i
theorem reverseRegisters_injective : Function.Injective reverseRegisters := Fin.castAdd_injective _ _
abbrev reverseAt (ports : Fin 4 ↪ Fin 24) : Cmd 8 24 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters ports)
def prefixReversePorts : Fin 4 ↪ Fin 24 := ⟨![12, 19, 13, 18], by decide⟩
def groupReversePorts : Fin 4 ↪ Fin 24 := ⟨![15, 19, 3, 18], by decide⟩

abbrev readOrigin : Cmd 8 24 := .seq (atom (.pop 0 0 1)) (readWord 0 9 (by decide))
abbrev readColumn : Cmd 8 24 := .seq (atom (.pop 4 0 1)) (readWord 4 10 (by decide))
abbrev pairStep : Cmd 8 24 := .seq readOrigin (.seq readColumn
  (.seq (emitFrame 10 11 (by decide)) (.seq (emitFrame 9 11 (by decide))
    (emitRecord 11 12 (by decide)))))
abbrev popCount : Cmd 8 24 := atom (.pop 8 5 4)
abbrev pairBody : Cmd 8 24 := .seq pairStep popCount
abbrev pairLoop : Cmd 8 24 := .while 5 pairBody
abbrev pairs : Cmd 8 24 := .seq popCount pairLoop

abbrev groupStep : Cmd 8 24 := .seq (readWord 5 6 (by decide))
  (.seq countScope (.seq (copy 7 8) (.seq (push 12 false) (.seq pairs
    (.seq (push 13 false) (.seq (reverseAt prefixReversePorts)
      (.seq (emitFrame 13 14 (by decide)) (.seq (emitFrame 7 14 (by decide))
        (emitRecord 14 15 (by decide))))))))))
abbrev popScope : Cmd 8 24 := atom (.pop 5 7 6)
abbrev groupBody : Cmd 8 24 := .seq groupStep popScope
abbrev groupLoop : Cmd 8 24 := .while 7 groupBody

abbrev command : Cmd 8 24 := .seq (copy 1 4) (.seq (copy 2 5)
  (.seq (push 15 false) (.seq popScope (.seq groupLoop
    (.seq (clear 0) (.seq (clear 4) (.seq (push 3 false)
      (reverseAt groupReversePorts))))))))
def program := compiled command 0 3

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
