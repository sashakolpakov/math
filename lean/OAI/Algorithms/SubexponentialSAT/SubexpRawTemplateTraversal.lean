import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateStorage

namespace OAI.Algorithms

/-! Measured fixed-control scans used by the raw template producer. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Store := Fin 288 → Word

def inputState (src : Fin 288) (regs : Fin 16 → Bool) (store : Store)
    (input : Word) : Data := ⟨regs, Function.update store src input⟩

def popTag (src : Fin 288) : Code := .base (.atom (.pop src 0 1))

theorem popTag_eval (src : Fin 288) (regs : Fin 16 → Bool) (store : Store)
    (bit : Bool) (rest : Word) :
    Eval (popTag src) 1 (inputState src regs store (bit :: rest))
      (inputState src (readRegs regs 0 1 (some bit)) store rest) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop src (0 : Fin 16) 1)
    (inputState src regs store (bit :: rest)))
  simpa [popTag, inputState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def afterTag {α : Type*} (src : Fin 288) (regs : Fin 16 → Bool) (store : Store)
    (encode : α → Word) (xs : List α) (rest : Word) : Data :=
  match xs with
  | [] => inputState src (readRegs regs 0 1 (some false)) store rest
  | x :: xs => inputState src (readRegs regs 0 1 (some true)) store
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest))

theorem popList_eval {α : Type*} (src : Fin 288) (regs : Fin 16 → Bool) (store : Store)
    (encode : α → Word) (xs : List α) (rest : Word) :
    Eval (popTag src) 1 (inputState src regs store (Encoding.encodeList encode xs ++ rest))
      (afterTag src regs store encode xs rest) := by
  cases xs with
  | nil => simpa only [Encoding.encodeList, List.singleton_append, afterTag] using
      popTag_eval src regs store false rest
  | cons x xs =>
      simpa only [Encoding.encodeList, List.cons_append, List.append_assoc, afterTag] using
        popTag_eval src regs store true
          (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest))

def scanBare (src : Fin 288) (body : Code) : Code :=
  .seq (popTag src) (.while 0 (.seq body (popTag src)))

def scanBudget {α : Type*} (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => cost x + 2)).sum

/-- The body is executed once for each actual frame, in input order.
Its specification is a hypothesis on a fixed command; enclosing producers
instantiate it with their concrete byte operations and selector calls. -/
theorem scanBare_eval {α : Type*} (src : Fin 288) (body : Code)
    (encode : α → Word) (cost : α → ℕ) (update : α → Store → Store)
    (inv : Store → Prop)
    (hbody : ∀ x regs store rest, inv store →
      ∃ n rf, n ≤ cost x ∧ Eval body n
        (inputState src regs store (Encoding.frame (encode x) ++ rest))
        (inputState src rf (update x store) rest))
    (hpreserve : ∀ x store, inv store → inv (update x store))
    (xs : List α) (regs : Fin 16 → Bool) (store : Store) (rest : Word) (hw : inv store) :
    ∃ n rf, n ≤ 2 + scanBudget cost xs ∧
      Eval (scanBare src body) n
        (inputState src regs store (Encoding.encodeList encode xs ++ rest))
        (inputState src rf (xs.foldl (fun s x => update x s) store) rest) := by
  have loop : ∀ (xs : List α) regs store, inv store →
      ∃ n rf, n ≤ 1 + scanBudget cost xs ∧
        Eval (.while 0 (.seq body (popTag src))) n
          (afterTag src regs store encode xs rest)
          (inputState src rf (xs.foldl (fun s x => update x s) store) rest) := by
    intro xs
    induction xs with
    | nil =>
      intro regs store hw
      refine ⟨1, readRegs regs 0 1 (some false), by simp [scanBudget], ?_⟩
      exact Eval.while_false (by simp [afterTag, inputState, readRegs])
    | cons x xs ih =>
      intro regs store hw
      let rp := readRegs regs 0 1 (some true)
      let tail := Encoding.encodeList encode xs ++ rest
      obtain ⟨nb, rf, hnb, hb⟩ := hbody x rp store tail hw
      have hp := popList_eval src rf (update x store) encode xs rest
      obtain ⟨nt, rt, hnt, ht⟩ := ih rf (update x store) (hpreserve x store hw)
      have he := Eval.while_true
        (by simp [afterTag, inputState, readRegs] :
          (afterTag src regs store encode (x :: xs) rest).regs 0 = true)
        (hb.seq hp) ht
      refine ⟨_, rt, ?_, he⟩
      simp only [scanBudget, List.map_cons, List.sum_cons] at *
      omega
  obtain ⟨n, rf, hn, he⟩ := loop xs regs store hw
  exact ⟨1 + n, rf, by omega, (popList_eval src regs store encode xs rest).seq he⟩

def recordBytes {α : Type*} (encode : α → Word) (xs : List α) : Word :=
  (xs.map (fun x => record (encode x))).flatten

theorem encodeList_eq_records {α : Type*} (encode : α → Word) (xs : List α) :
    Encoding.encodeList encode xs = recordBytes encode xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [Encoding.encodeList, recordBytes, record, ih, List.append_assoc]

theorem recordFold_eq {α : Type*} (encode : α → Word) (xs : List α) (old : Word) :
    xs.foldl (fun acc x => (record (encode x)).reverse ++ acc) old =
      (recordBytes encode xs).reverse ++ old := by
  induction xs generalizing old with
  | nil => simp [recordBytes]
  | cons x xs ih =>
    simp [List.foldl_cons, ih, recordBytes, List.reverse_append, List.append_assoc]

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
