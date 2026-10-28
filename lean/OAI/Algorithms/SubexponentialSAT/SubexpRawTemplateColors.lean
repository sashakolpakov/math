import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateColor

namespace OAI.Algorithms

/-! The measured runtime-color loop over the actual inner-bank list stream. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {D r Q Δ : ℕ}

def groupsFrom
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) :
    ℕ → List (List Word) → List Word
  | _, [] => []
  | start, increments :: remaining =>
      if hg : start < r then
        colorGroupBytes P t items ⟨start, hg⟩ increments ::
          groupsFrom P t items (start + 1) remaining
      else []

def groupScanCost
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word) :
    ℕ → List (List Word) → ℕ
  | _, [] => 0
  | start, increments :: remaining =>
      if hg : start < r then
        groupStepCost P t items suffix ⟨start, hg⟩ increments + 2 +
          groupScanCost P t items suffix (start + 1) remaining
      else 0

def groupsStore
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (start : ℕ) (inners : List (List Word)) (store : Store) : Store :=
  Function.update
    (Function.update store 211
      ((recordBytes id (groupsFrom P t items start inners)).reverse ++ store 211))
    219 (colorWord (start + inners.length))

theorem source_masters
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (store : Store) (input : Word) (hm : Masters P t items suffix store) :
    Masters P t items suffix (Function.update store 204 input) := by
  apply hm.of_frame
  intro i hi
  simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

theorem source_work (store : Store) (input : Word) (hw : ColorWork store) :
    ColorWork (Function.update store 204 input) := by
  constructor
  · intro i hlo hhi
    have h204 : i ≠ 204 := by intro h; subst i; norm_num at hhi
    simpa [h204] using hw.workspace i hlo hhi
  · simpa using hw.bank
  · simpa using hw.payload
  · simpa using hw.support
  · simpa using hw.factors
  · simpa using hw.term
  · simpa using hw.terms
  · simpa using hw.group
  · simpa using hw.scratch
  · simpa using hw.outside
  · simpa using hw.forward

theorem groupsStore_nil
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (start : ℕ) (store : Store) (hcolor : store 219 = colorWord start) :
    groupsStore P t items start [] store = store := by
  funext i
  by_cases h211 : i = 211
  · subst i; simp [groupsStore, groupsFrom, recordBytes]
  by_cases h219 : i = 219
  · subst i; simp [groupsStore, hcolor]
  · simp [groupsStore, h211, h219]

theorem groupsStore_step
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (start : ℕ) (hg : start < r) (increments : List Word)
    (remaining : List (List Word)) (store : Store) :
    groupsStore P t items (start + 1) remaining
        (colorStore P t items ⟨start, hg⟩ increments store) =
      groupsStore P t items start (increments :: remaining) store := by
  funext i
  by_cases h211 : i = 211
  · subst i
    simp [groupsStore, groupsFrom, hg, colorStore, recordBytes,
      List.reverse_append, List.append_assoc]
  by_cases h219 : i = 219
  · subst i
    simp [groupsStore, Nat.add_comm, Nat.add_left_comm]
  · simp [groupsStore, colorStore, h211, h219]

/-- Color indices are read from the actual binary counter. The list length
bound ensures each selector call receives a valid color; no lookup table
or machine control depends on the number of colors. -/
theorem colors_eval
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (inners : List (List Word)) (start : ℕ) (hbound : start + inners.length ≤ r)
    (regs : Fin 16 → Bool) (store : Store) (rest : Word)
    (hm : Masters P t items suffix store) (hw : ColorWork store)
    (hcolor : store 219 = colorWord start) :
    ∃ n rf, n ≤ 2 + groupScanCost P t items suffix start inners ∧
      Eval (scanBare 204 groupBody) n
        (inputState 204 regs store (Encoding.encodeList (Encoding.encodeList id) inners ++ rest))
        (inputState 204 rf (groupsStore P t items start inners store) rest) := by
  have loop : ∀ (remaining : List (List Word)) (start : ℕ),
      start + remaining.length ≤ r → ∀ regs store,
      Masters P t items suffix store → ColorWork store → store 219 = colorWord start →
      ∃ n rf, n ≤ 1 + groupScanCost P t items suffix start remaining ∧
        Eval (.while 0 (.seq groupBody (popTag 204))) n
          (afterTag 204 regs store (Encoding.encodeList id) remaining rest)
          (inputState 204 rf (groupsStore P t items start remaining store) rest) := by
    intro remaining
    induction remaining with
    | nil =>
      intro start hb regs store hm hw hc
      refine ⟨1, readRegs regs 0 1 (some false), by simp [groupScanCost], ?_⟩
      rw [groupsStore_nil P t items start store hc]
      exact Eval.while_false (by simp [afterTag, inputState, readRegs])
    | cons increments remaining ih =>
      intro start hb regs store hm hw hc
      have hg : start < r := by simp only [List.length_cons] at hb; omega
      let g : Fin r := ⟨start, hg⟩
      let tail := Encoding.encodeList (Encoding.encodeList id) remaining ++ rest
      let a := afterTag 204 regs store (Encoding.encodeList id) (increments :: remaining) rest
      have hma : Masters P t items suffix a.stacks :=
        source_masters P t items suffix store _ hm
      have hwa : ColorWork a.stacks := source_work store _ hw
      obtain ⟨nb, e, hnb, he, hse⟩ := groupBody_eval P t items suffix g increments tail a hma hwa
        (by simp [a, afterTag, inputState, tail]) (by simpa [a, afterTag, inputState, g] using hc)
      let nextStore := colorStore P t items g increments store
      have heq : e = inputState 204 e.regs nextStore tail := by
        apply state_ext
        · rfl
        · rw [hse]
          funext i
          by_cases h204 : i = 204
          · subst i; simp [inputState]
          by_cases h211 : i = 211
          · subst i; simp [inputState, nextStore, colorStore, a, afterTag]
          by_cases h219 : i = 219
          · subst i; simp [inputState, nextStore, colorStore, a, afterTag]
          · simp [inputState, nextStore, colorStore, a, afterTag, h204, h211, h219]
      rw [heq] at he
      have hp := popList_eval 204 e.regs nextStore (Encoding.encodeList id) remaining rest
      have hnext : start + 1 + remaining.length ≤ r := by
        simp only [List.length_cons] at hb; omega
      obtain ⟨nt, rt, hnt, ht⟩ := ih (start + 1) hnext e.regs nextStore
        (colorStore_masters P t items suffix g increments store hm)
        (colorStore_work P t items g increments store hw)
        (by simp [nextStore, colorStore, g])
      have hend : groupsStore P t items (start + 1) remaining nextStore =
          groupsStore P t items start (increments :: remaining) store :=
        groupsStore_step P t items start hg increments remaining store
      rw [hend] at ht
      have hh := Eval.while_true
        (by simp [a, afterTag, inputState, readRegs] : a.regs 0 = true)
        (he.seq hp) ht
      refine ⟨_, rt, ?_, hh⟩
      simp only [groupScanCost, dite_eq_left hg]
      dsimp [g] at hnb
      omega
  obtain ⟨n, rf, hn, he⟩ := loop inners start hbound regs store hm hw hcolor
  exact ⟨1 + n, rf, by omega,
    (popList_eval 204 regs store (Encoding.encodeList id) inners rest).seq he⟩

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
