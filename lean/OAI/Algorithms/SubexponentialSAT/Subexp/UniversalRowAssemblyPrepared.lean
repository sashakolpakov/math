import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowInputTypes

namespace OAI.Algorithms

/-! Concrete, ordered cache tables for the universal-row producer. -/

namespace SubexponentialSAT.Subexp.UniversalRowAssembly

open BitProgram StructuredCalls
open UniversalRowWorkspace (port)

variable {r Q Δ : ℕ}
variable (p : ℕ) [Fact p.Prime] (i : Fin Δ)
variable (u y : MulticolorTypes.UniversalType r Q Δ) (xs : List (ZMod p))

/-- The value array is defined from the matrix entries actually computed by
the vector program. All field caches follow the same increasing Fin Q order. -/
def computedTables (inverse negative : Fin Q → Word) (difference : Fin Q → Fin Q → Word) :
    UniversalRowLoop.Tables where
  values := (List.range' 0 Q).map (CorrectionVectorProgram.bytesAt p i u y xs)
  inverses := List.ofFn inverse
  negatives := List.ofFn negative
  differences := List.ofFn (fun j => List.ofFn (difference j))

theorem computedTables_values (inverse negative : Fin Q → Word)
    (difference : Fin Q → Fin Q → Word) :
    (computedTables p i u y xs inverse negative difference).values.flatten =
      CorrectionVectorProgram.vector p i u y xs 0 Q := rfl

private theorem selected_lt (j : ℕ) (hj : j ∈ selected i u y) : j < Q := by
  obtain ⟨k, _, hk⟩ := List.mem_map.mp hj
  exact hk ▸ k.isLt

private theorem flatten_width (rows : List Word) (width : ℕ)
    (hw : ∀ row ∈ rows, row.length = width) : rows.flatten.length = rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hh := hw row (by simp)
      have ht := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.flatten_cons, List.length_append, List.length_cons, hh, ht,
        Nat.add_mul, Nat.one_mul]
      omega

theorem computedTables_valid (inverse negative : Fin Q → Word)
    (difference : Fin Q → Fin Q → Word) (width rowWidth : Word)
    (hw : width.length = 4 * MatrixWordEncoding.width p)
    (hrw : rowWidth.length = Q * (4 * MatrixWordEncoding.width p))
    (hi : ∀ j, (inverse j).length = 4 * MatrixWordEncoding.width p)
    (hn : ∀ j, (negative j).length = 4 * MatrixWordEncoding.width p)
    (hd : ∀ j k, (difference j k).length = 4 * MatrixWordEncoding.width p) :
    UniversalRowLoop.Valid (computedTables p i u y xs inverse negative difference)
      width rowWidth (selected i u y) := by
  constructor
  · intro row hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hrow
    simpa only [CorrectionVectorProgram.bytesAt_length] using hw.symm
  · intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    exact (hi j).trans hw.symm
  · intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    exact (hn j).trans hw.symm
  · intro row hrow
    obtain ⟨cells, hcells, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hcells
    rw [flatten_width _ (4 * MatrixWordEncoding.width p)]
    · simpa using hrw.symm
    · intro cell hcell
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hcell
      exact hd j k
  · intro j hj
    have hlt := selected_lt i u y j hj
    simpa [computedTables] using And.intro hlt (And.intro hlt hlt)
  · intro j hj row hrow
    have hlt := selected_lt i u y j hj
    change row ∈ (List.ofFn (fun k : Fin Q => List.ofFn (difference k))).getD j [] at hrow
    rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn] at hrow
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hrow
    exact (hd ⟨j, hlt⟩ k).trans hw.symm
  · intro j hj k hk
    have hjlt := selected_lt i u y j hj
    have hklt := selected_lt i u y k hk
    change k < ((List.ofFn (fun j : Fin Q => List.ofFn (difference j))).getD j []).length ∧
      k < (List.ofFn negative).length
    rw [List.getD_eq_getElem _ _ (by simpa using hjlt), List.getElem_ofFn]
    simpa using And.intro hklt hklt

/-- Physical input invariants for one row. The matrix coefficients are the
normalized scalar-search output. The three field caches are raw arrays in
the established node order, not a supplied interpolation expression. -/
structure PreparedInput (inverse negative : Fin Q → Word)
    (difference : Fin Q → Fin Q → Word) (a : Data) : Prop where
  empty : ∀ j : Fin 49, a.stacks (port j) = []
  code : a.stacks 26 = []
  positions : a.stacks 253 = List.replicate Q true
  colors : a.stacks 252 = List.replicate r true
  degree : a.stacks 243 = List.replicate (xs.length + 1) true
  width : (a.stacks 129).length = MatrixWordEncoding.width p
  zero : a.stacks 131 = List.replicate (4 * MatrixWordEncoding.width p) false
  constantWidth : (a.stacks 133).length = MatrixWordEncoding.width p
  constantValue : BinaryArithmetic.toNat (a.stacks 133) = p - 1
  left : a.stacks 272 = CollisionProgram.encodeType u
  right : a.stacks 275 = CollisionProgram.encodeType y
  slot : a.stacks 284 = List.replicate (i.val + 1) true
  modulus : a.stacks 128 = MatrixWordEncoding.modulus p
  coefficients : a.stacks 254 = MatrixProgramSupport.words (xs.map (MatrixWordEncoding.word p))
  inverseArray : a.stacks 135 = (List.ofFn inverse).flatten
  negativeArray : a.stacks 136 = (List.ofFn negative).flatten
  differenceArray : a.stacks 137 = (List.ofFn (fun j => (List.ofFn (difference j)).flatten)).flatten
  nodeArrayWidth : (a.stacks 134).length = Q * (4 * MatrixWordEncoding.width p)
  inverseWidth : ∀ j, (inverse j).length = 4 * MatrixWordEncoding.width p
  negativeWidth : ∀ j, (negative j).length = 4 * MatrixWordEncoding.width p
  differenceWidth : ∀ j k, (difference j k).length = 4 * MatrixWordEncoding.width p

/-- The complete fixed command computes the row from the physical masters,
generates its mismatch list, and returns all scratch stacks to empty. -/
theorem command_eval_prepared (h2 : (2 : ZMod p) ≠ 0)
    (inverse negative : Fin Q → Word) (difference : Fin Q → Fin Q → Word)
    (a : Data) (h : PreparedInput p i u y xs inverse negative difference a) :
    ∃ n ≤ executionBound p i u y xs (computedTables p i u y xs inverse negative difference) a,
      ∃ b : Data, Eval command n a b ∧
        b.stacks = Function.update a.stacks 26
          (sourceWord p i u y xs (computedTables p i u y xs inverse negative difference) a) := by
  apply command_eval_from_inputs p i u y xs h2
    (computedTables p i u y xs inverse negative difference) a
    h.empty h.code h.positions h.colors h.degree h.width h.zero h.constantWidth h.constantValue
  · intro regs
    exact UniversalRowInputTypes.inputStacks_eq_vector a p i u y xs (a.stacks 133)
      (a.stacks 131) regs h.positions h.colors h.left h.right h.slot h.modulus h.coefficients rfl rfl
  · intro regs j
    exact congrFun (UniversalRowInputTypes.inputStacks_first29 a xs.length (MatrixWordEncoding.width p)
      i u y regs h.positions h.colors h.left h.right h.slot) j
  · exact computedTables_values p i u y xs inverse negative difference
  · exact h.inverseArray
  · exact h.negativeArray
  · rw [h.differenceArray]
    simp [computedTables, UniversalRowLoop.Tables.rows]
    rfl
  · exact computedTables_valid p i u y xs inverse negative difference (a.stacks 131) (a.stacks 134)
      (by simp [h.zero]) h.nodeArrayWidth h.inverseWidth h.negativeWidth h.differenceWidth

theorem program_runsIn_prepared (h2 : (2 : ZMod p) ≠ 0)
    (inverse negative : Fin Q → Word) (difference : Fin Q → Fin Q → Word)
    (a : Data) (h : PreparedInput p i u y xs inverse negative difference a) :
    ∃ b : Data, RunsIn program
      (executionBound p i u y xs (computedTables p i u y xs inverse negative difference) a + 1)
      (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks = Function.update a.stacks 26
        (sourceWord p i u y xs (computedTables p i u y xs inverse negative difference) a) := by
  obtain ⟨n, hn, b, he, hs⟩ := command_eval_prepared p i u y xs h2 inverse negative difference a h
  exact ⟨b, ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 272 26⟩, hs⟩

theorem primitive_runsIn_prepared (h2 : (2 : ZMod p) ≠ 0)
    (inverse negative : Fin Q → Word) (difference : Fin Q → Fin Q → Word)
    (a : Data) (h : PreparedInput p i u y xs inverse negative difference a) :
    ∃ b : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (executionBound p i u y xs (computedTables p i u y xs inverse negative difference) a + 1))
      (BitProgram.primitiveCfg program (a.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (b.withPC none)) ∧
      b.stacks = Function.update a.stacks 26
        (sourceWord p i u y xs (computedTables p i u y xs inverse negative difference) a) := by
  obtain ⟨b, he, hs⟩ := program_runsIn_prepared p i u y xs h2 inverse negative difference a h
  exact ⟨b, BitProgram.primitive_execution program he, hs⟩

/-- The 25-register dispatcher receives the exact source word and retains
its nine high metadata registers. Its type metadata and caches are framed. -/
theorem caller_eval_prepared (h2 : (2 : ZMod p) ≠ 0)
    (inverse negative : Fin Q → Word) (difference : Fin Q → Fin Q → Word)
    (a : State 25 288)
    (h : PreparedInput p i u y xs inverse negative difference (projectState (Fin.castAdd 9) id a)) :
    ∃ n ≤ executionBound p i u y xs (computedTables p i u y xs inverse negative difference)
        (projectState (Fin.castAdd 9) id a) + 1,
      ∃ b : State 25 288, Eval callerCommand n a b ∧
        b.stacks = Function.update a.stacks 26
          (sourceWord p i u y xs (computedTables p i u y xs inverse negative difference)
            (projectState (Fin.castAdd 9) id a)) ∧
        (∀ j : Fin 25, 16 ≤ j.val → b.regs j = a.regs j) := by
  obtain ⟨inner, ⟨n, hn, he⟩, hs⟩ := program_runsIn_prepared p i u y xs h2 inverse negative
    difference (projectState (Fin.castAdd 9) id a) h
  let b := embedState (Fin.castAdd 9) id a inner
  have ht := eval_call_from_state program (Fin.castAdd 9) id a
    (Fin.castAdd_injective 16 9) Function.injective_id he
  refine ⟨n, hn, b, ht, ?_, ?_⟩
  · funext j
    rw [show b.stacks j = inner.stacks j from
      embedState_stack (Fin.castAdd 9) id a inner Function.injective_id j, hs]
    rfl
  · intro j hj
    apply embedState_register_frame
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    change k.val = j.val at hv
    omega

end SubexponentialSAT.Subexp.UniversalRowAssembly

end OAI.Algorithms
