import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableExecution
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Polynomial cost of the actual dense row-table traversal

The numeric row bounds below are required only at the factor/vertex/coordinate
triples visited by the supplied scope list. The separate `FactorRows` premise
still supplies actual executions of one fixed row program at the live states.
The final budget includes the compiled halt instruction.
-/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

/-- Bounds on the rows actually requested by the scope traversal, beginning
at physical factor counter `e`. No cost is assumed at other triples. -/
def RowBounds (render : ℕ → ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ → ℕ)
    (D C B : ℕ) : ℕ → List (List ℕ) → Prop
  | _, [] => True
  | e, vertices :: rest =>
      (∀ v ∈ vertices, ∀ j < D, cost e v j ≤ C ∧ (render e v j).length ≤ B) ∧
      RowBounds render cost D C B (e + 1) rest

theorem coordinateWord_length_le (render : ℕ → Word) (D B : ℕ)
    (hb : ∀ j < D, (render j).length ≤ B) (word : Word)
    (hw : word ∈ coordinateWords render D) : word.length ≤ B := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
  exact hb j (List.mem_range.mp hj)

theorem coordinateCode_length_le (render : ℕ → Word) (D B : ℕ)
    (hb : ∀ j < D, (render j).length ≤ B) :
    (Encoding.encodeList id (coordinateWords render D)).length ≤ 1 + D * (2 * B + 2) := by
  have h := Encoding.length_encodeList_upper id (coordinateWords render D) B
    (coordinateWord_length_le render D B hb)
  simpa [coordinateWords, Nat.mul_comm] using h

theorem coordinateReverseCode_length_le (render : ℕ → Word) (D B : ℕ)
    (hb : ∀ j < D, (render j).length ≤ B) :
    (Encoding.encodeList id (coordinateWords render D).reverse).length ≤
      1 + D * (2 * B + 2) := by
  have h := Encoding.length_encodeList_upper id (coordinateWords render D).reverse B
    (fun word hw => coordinateWord_length_le render D B hb word (by simpa using hw))
  simpa [coordinateWords, Nat.mul_comm] using h

theorem coordinateRunCost_le (render : ℕ → Word) (cost : ℕ → ℕ) (D C B : ℕ)
    (hc : ∀ j < D, cost j ≤ C) (hb : ∀ j < D, (render j).length ≤ B) :
    coordinateRunCost render cost D ≤ D * (C + 25 * B + 41) + 24 := by
  have hloop := coordinateBudget_le render cost 0 D C B
    (fun j _ hj => hc j (by simpa using hj))
    (fun j _ hj => hb j (by simpa using hj))
  have hcode := coordinateReverseCode_length_le render D B hb
  unfold coordinateRunCost
  nlinarith

theorem incidenceCost_le (render : ℕ → Word) (cost : ℕ → ℕ) (D C B v : ℕ)
    (hc : ∀ j < D, cost j ≤ C) (hb : ∀ j < D, (render j).length ≤ B) :
    incidenceCost render cost D v ≤ D * (C + 41 * B + 57) + 2 * v + 49 := by
  have hrun := coordinateRunCost_le render cost D C B hc hb
  have hcode := coordinateCode_length_le render D B hb
  unfold incidenceCost
  nlinarith

private theorem scope_head_bound (K v : ℕ) :
    6 * (v + 1) + (K + 2 * v + 49) + 7 ≤ (2 * (v + 1) + 2) * (K + 62) := by
  ring_nf
  omega

theorem scopeBudget_le (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ)
    (D C B : ℕ) (vertices : List ℕ)
    (hrows : ∀ v ∈ vertices, ∀ j < D, cost v j ≤ C ∧ (render v j).length ≤ B) :
    scopeBudget render cost D vertices ≤
      (scopeCode vertices).length * (D * (C + 41 * B + 57) + 62) := by
  induction vertices with
  | nil => simp [scopeBudget, scopeCode]
  | cons v vs ih =>
      have hv := incidenceCost_le (render v) (cost v) D C B v
        (fun j hj => (hrows v (by simp) j hj).1)
        (fun j hj => (hrows v (by simp) j hj).2)
      have ht := ih (fun w hw j hj => hrows w (by simp [hw]) j hj)
      have hh := scope_head_bound (D * (C + 41 * B + 57)) v
      rw [scopeBudget, Encoding.length_encodeNat]
      calc
        _ ≤ (2 * (v + 1) + 2) * (D * (C + 41 * B + 57) + 62) +
            (scopeCode vs).length * (D * (C + 41 * B + 57) + 62) := by omega
        _ = (scopeCode (v :: vs)).length * (D * (C + 41 * B + 57) + 62) := by
          simp only [scopeCode, Encoding.length_encodeList_cons, Encoding.length_encodeNat]
          ring

private theorem factor_head_bound (K L : ℕ) :
    9 * L + 18 + L * (K + 62) ≤ (2 * L + 2) * (K + 80) := by
  ring_nf
  omega

theorem factorFoldBudget_le (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D C B e : ℕ) (scopes : List (List ℕ))
    (initial : Store) (he : initial 261 = unary e)
    (hrows : RowBounds render cost D C B e scopes) :
    foldBudget scopeCode (factorStep render D) (factorCost render cost D) initial scopes ≤
      (scopesCode scopes).length * (D * (C + 41 * B + 57) + 80) := by
  induction scopes generalizing initial e with
  | nil => simp [foldBudget, scopesCode]
  | cons vertices rest ih =>
      have hlen : (initial 261).length = e := by simpa [unary] using congrArg List.length he
      have hs : factorStep render D vertices initial 261 = unary (e + 1) := by
        simp [factorStep, he, unary, List.replicate_succ]
      have ht := ih (e := e + 1) (initial := factorStep render D vertices initial) hs hrows.2
      have hscope := scopeBudget_le (render e) (cost e) D C B vertices hrows.1
      have hhead : 6 * (scopeCode vertices).length + factorCost render cost D vertices initial + 7 ≤
          (2 * (scopeCode vertices).length + 2) * (D * (C + 41 * B + 57) + 80) := by
        unfold factorCost
        simp only [hlen]
        calc
          _ ≤ 9 * (scopeCode vertices).length + 18 +
              (scopeCode vertices).length * (D * (C + 41 * B + 57) + 62) := by omega
          _ ≤ _ := factor_head_bound _ _
      rw [foldBudget]
      calc
        _ ≤ (2 * (scopeCode vertices).length + 2) * (D * (C + 41 * B + 57) + 80) +
            (scopesCode rest).length * (D * (C + 41 * B + 57) + 80) := Nat.add_le_add hhead ht
        _ = (scopesCode (vertices :: rest)).length * (D * (C + 41 * B + 57) + 80) := by
          simp only [scopesCode, Encoding.length_encodeList_cons]
          ring

theorem incidenceCount_le_scopeLength (scopes : List (List ℕ)) :
    (scopes.map List.length).sum ≤ (scopesCode scopes).length := by
  induction scopes with
  | nil => simp [scopesCode]
  | cons vertices rest ih =>
      have hv := Encoding.length_encodeList_lower Encoding.encodeNat vertices
      change vertices.length + 1 ≤ (scopeCode vertices).length at hv
      simp only [List.map_cons, List.sum_cons, scopesCode, Encoding.length_encodeList_cons] at ⊢
      change (rest.map List.length).sum ≤ (Encoding.encodeList scopeCode rest).length at ih
      omega

theorem incidenceWord_length_le (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D C B e : ℕ) (scopes : List (List ℕ))
    (hrows : RowBounds render cost D C B e scopes) (word : Word)
    (hw : word ∈ incidenceRows render D e scopes) :
    word.length ≤ 1 + D * (2 * B + 2) := by
  induction scopes generalizing e with
  | nil => simp [incidenceRows] at hw
  | cons vertices rest ih =>
      simp only [incidenceRows, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        exact coordinateCode_length_le (render e v) D B
          (fun j hj => (hrows.1 v hv j hj).2)
      · exact ih (e := e + 1) hrows.2 hw

theorem incidenceReverseCode_length_le (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D C B e : ℕ) (scopes : List (List ℕ))
    (hrows : RowBounds render cost D C B e scopes) :
    (Encoding.encodeList id (incidenceRows render D e scopes).reverse).length ≤
      1 + (scopesCode scopes).length * (2 * (1 + D * (2 * B + 2)) + 2) := by
  have hcode := Encoding.length_encodeList_upper id (incidenceRows render D e scopes).reverse
    (1 + D * (2 * B + 2))
    (fun word hw => incidenceWord_length_le render cost D C B e scopes hrows word (by simpa using hw))
  have hcount := incidenceCount_le_scopeLength scopes
  simp only [List.length_reverse, incidenceRows_length] at hcode
  calc
    _ ≤ 1 + (2 * (1 + D * (2 * B + 2)) + 2) * (scopes.map List.length).sum := hcode
    _ ≤ 1 + (2 * (1 + D * (2 * B + 2)) + 2) * (scopesCode scopes).length := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hcount) _
    _ = _ := by ring

/-- `N` is the encoded scope-list length, `D` the runtime dimension, and `L`
the lookup word length. `C` and `B` bound only visited row costs and lengths. -/
def tablePolynomialBound (N D C B L : ℕ) : ℕ :=
  200 * (N + 1) * (D + 1) * (C + B + L + 1)

theorem tableRunCost_add_one_le (a : Data) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D C B : ℕ) (scopes : List (List ℕ))
    (ha : TableReady a D scopes) (hrows : RowBounds render cost D C B 0 scopes) :
    tableRunCost a render cost D scopes + 1 ≤
      tablePolynomialBound (scopesCode scopes).length D C B (a.stacks 265).length := by
  have h261 : a.stacks 261 = [] := ha.2.2 _ (by simp)
  have hcounter : (tablePrepared a).stacks 261 = unary 0 := by
    simp [tablePrepared, pushed, copied, StackRoutines.copyStacks, h261, unary]
  have hfold := factorFoldBudget_le render cost D C B 0 scopes (tablePrepared a).stacks hcounter hrows
  have hcode := incidenceReverseCode_length_le render cost D C B 0 scopes hrows
  have hcount := Encoding.length_encodeList_lower scopeCode scopes
  change scopes.length + 1 ≤ (scopesCode scopes).length at hcount
  calc
    _ ≤ (scopesCode scopes).length * (D * (C + 41 * B + 57) + 80) +
        9 * (scopesCode scopes).length + 2 * (scopesCode scopes).length +
        2 * D + 2 * (a.stacks 265).length + 25 +
        10 * (1 + (scopesCode scopes).length * (2 * (1 + D * (2 * B + 2)) + 2)) := by
      unfold tableRunCost
      omega
    _ ≤ _ := by
      unfold tablePolynomialBound
      ring_nf
      omega

/-- One fixed row program and one fixed traversal, with actual callback runs
and bounds only on the visited numeric row indices. Includes the final halt. -/
theorem program_runsIn_polynomial (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (a : Data) (D C B : ℕ) (scopes : List (List ℕ))
    (ha : TableReady a D scopes)
    (hexec : FactorRows row render cost D (tablePrepared a).stacks scopes)
    (hrows : RowBounds render cost D C B 0 scopes) :
    ∃ regs, RunsIn (program row)
      (tablePolynomialBound (scopesCode scopes).length D C B (a.stacks 265).length)
      (a.withPC (some (program row).entry))
      ((tableResult a regs render D scopes).withPC none) := by
  obtain ⟨regs, n, hn, ht⟩ := program_runsIn row render cost a D scopes ha hexec
  exact ⟨regs, n, hn.trans (tableRunCost_add_one_le a render cost D C B scopes ha hrows), ht⟩

/-- The same concrete bounded run on the primitive machine. The overhead
depends only on the fixed row/traversal program, not on runtime table data. -/
theorem primitive_runsIn_polynomial (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (a : Data) (D C B : ℕ) (scopes : List (List ℕ))
    (ha : TableReady a D scopes)
    (hexec : FactorRows row render cost D (tablePrepared a).stacks scopes)
    (hrows : RowBounds render cost D C B 0 scopes) :
    ∃ regs, Computation.RunsIn (primitive (program row)).step
      (primitiveOverhead (program row) *
        tablePolynomialBound (scopesCode scopes).length D C B (a.stacks 265).length)
      (primitiveCfg (program row) (a.withPC (some (program row).entry)))
      (primitiveCfg (program row) ((tableResult a regs render D scopes).withPC none)) := by
  obtain ⟨regs, ht⟩ := program_runsIn_polynomial row render cost a D C B scopes ha hexec hrows
  exact ⟨regs, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.SubexpDenseRowTableProgram

end OAI.Algorithms
