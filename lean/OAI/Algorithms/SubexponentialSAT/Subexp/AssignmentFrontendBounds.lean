import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentFrontendNumericBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentFrontendProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontendBounds

namespace OAI.Algorithms

/-!
# A polynomial bound for the complete assignment frontend

The size parameter contains only the actual input scope bytes and numerical
parameters, including the universal type count. Generated pair tables,
alphabets and seed records are bounded inside the proof.
-/

namespace SubexponentialSAT.Subexp.AssignmentFrontendBounds

open BitProgram StructuredCalls MulticolorTypes

theorem pair_sourceBudget_le (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    AssignmentPairFrontend.sourceBudget D Δ scopes ≤
      2000000 * sourceSize r Q Δ D scopes ^ 5 :=
  (AssignmentPairFrontend.sourceBudget_le_polynomial D Δ scopes hd).trans
    (pair_polynomial_le r Q Δ D scopes)

/-- The intermediate pair tape is produced on an initially empty stack by
the actual frontend. Its length is therefore bounded by its actual steps. -/
theorem pairBytes_length_le (r Q Δ D : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    (AssignmentPairFrontend.pairBytes D Δ scopes).length ≤
      2000000 * sourceSize r Q Δ D scopes ^ 5 := by
  obtain ⟨rf, t, ht, he⟩ := AssignmentPairFrontend.program_run
    (fun _ => false) r Q Δ D scopes hd
  have h := SequentialProgram.trace_stack_length_le he (45 : Fin 48)
  have hp : (AssignmentPairFrontend.pairBytes D Δ scopes).length ≤ t := by
    simpa [AssignmentPairFrontend.inputState, AssignmentInputProgram.inputState,
      StructuredProgram.State.withPC] using h
  exact (hp.trans ht).trans (pair_sourceBudget_le r Q Δ D scopes hd)

theorem input_extent_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    AssignmentInputProgram.extent r Q Δ D scopes.length
      (AssignmentPairFrontend.pairBytes D Δ scopes) ≤
        2000100 * sourceSize r Q Δ D scopes ^ 5 := by
  apply (AssignmentInputProgram.extent_le_sizeBound r Q Δ D scopes.length _ hr).trans
  exact input_expression_le r Q Δ D scopes _ hr (pairBytes_length_le r Q Δ D scopes hd)

theorem input_extent_succ_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    AssignmentInputProgram.extent r Q Δ D scopes.length
      (AssignmentPairFrontend.pairBytes D Δ scopes) + 1 ≤
        inputCoefficient * sourceSize r Q Δ D scopes ^ 5 := by
  have h := input_extent_le r Q Δ D scopes hr hd
  have hpos : 1 ≤ sourceSize r Q Δ D scopes ^ 5 :=
    Nat.one_le_pow _ _ (sourceSize_pos r Q Δ D scopes)
  unfold inputCoefficient
  omega

theorem input_budget_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    AssignmentInputProgram.budget r Q Δ D scopes.length
      (AssignmentPairFrontend.pairBytes D Δ scopes) ≤
        (20000 * inputCoefficient ^ 4) * sourceSize r Q Δ D scopes ^ 20 := by
  apply (AssignmentInputProgram.budget_le r Q Δ D scopes.length _ hr).trans
  calc
    _ ≤ 20000 * (inputCoefficient * sourceSize r Q Δ D scopes ^ 5) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (input_extent_succ_le r Q Δ D scopes hr hd) 4)
    _ = _ := by ring

theorem init_budget_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    AssignmentInitProgram.sourceCost (AssignmentInputProgram.context r Q Δ D scopes.length
      (AssignmentPairFrontend.pairBytes D Δ scopes)) ≤
        (40 * inputCoefficient ^ 2) * sourceSize r Q Δ D scopes ^ 10 := by
  let bits := AssignmentPairFrontend.pairBytes D Δ scopes
  let B := AssignmentInputProgram.extent r Q Δ D scopes.length bits
  have hc := AssignmentInitProgram.sourceCost_le
    (AssignmentInputProgram.context r Q Δ D scopes.length bits) B
    (by dsimp [B, AssignmentInputProgram.context, AssignmentInputProgram.extent]; omega)
    (by dsimp [B, AssignmentInputProgram.context, AssignmentInputProgram.extent]; omega)
    (by dsimp [B, AssignmentInputProgram.context, AssignmentInputProgram.extent]; omega)
  apply hc.trans
  calc
    _ ≤ 40 * (inputCoefficient * sourceSize r Q Δ D scopes ^ 5) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (input_extent_succ_le r Q Δ D scopes hr hd) 2)
    _ = _ := by ring

theorem score_budget_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r) :
    AssignmentFrontendProgram.scoreBound r Q Δ D scopes.length ≤
      scoreCoefficient * sourceSize r Q Δ D scopes ^ 50 :=
  score_expression_le r Q Δ D scopes hr

/-- Every intermediate byte length and scoring cost is derived above. Only
the actual incidence bound and positive color count remain as input facts. -/
theorem sourceBudget_le (r Q Δ D : ℕ) (scopes : List (List ℕ)) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    AssignmentFrontendProgram.sourceBudget r Q Δ D scopes ≤
      coefficient * sourceSize r Q Δ D scopes ^ 60 := by
  exact total_expression_le (sourceSize r Q Δ D scopes) _ _ _ _ _ _
    (sourceSize_pos r Q Δ D scopes)
    (pair_sourceBudget_le r Q Δ D scopes hd)
    (input_budget_le r Q Δ D scopes hr hd)
    (init_budget_le r Q Δ D scopes hr hd)
    (score_budget_le r Q Δ D scopes hr)
    (selection_budget_le r Q Δ D scopes hr)
    (seedCount_le r Q Δ D scopes)

/-- The complete fixed assignment program, with its generated inputs and
semantic output, obeys one polynomial whose degree and coefficient do not
vary with the instance parameters. -/
theorem program_run_polynomial (regs : Fin 16 → Bool) (r Q Δ D : ℕ) [NeZero r]
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q), ∃ e : AssignmentFrontendProgram.Data,
      (a :: tail).Nodup ∧ (∀ w, w ∈ a :: tail) ∧
      (a :: tail).map ReadPlan.encodeWord = AssignmentAlphabetSemantics.wordBytes r Q ∧
      RunsIn AssignmentFrontendProgram.program
        (coefficient * sourceSize r Q Δ D scopes ^ 60)
        ((AssignmentPairFrontend.inputState regs r Q Δ D scopes).withPC
          (some AssignmentFrontendProgram.program.entry))
        (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues
        (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
        a tail (List.finRange D)
        (AssignmentEnumeration.seedIndices (List.finRange D)
          (List.finRange scopes.length) Δ)).reverse.map ReadPlan.encodeWord).flatten ∧
      AssignmentFrontendProgram.RuntimeReady
        (AssignmentInputProgram.context r Q Δ D scopes.length
          (AssignmentPairFrontend.pairBytes D Δ scopes)) e := by
  obtain ⟨a, tail, e, hn, hf, hwords, ⟨t, ht, he⟩, ho, hready⟩ :=
    AssignmentFrontendProgram.program_run_framed regs r Q Δ D scopes hd
  exact ⟨a, tail, e, hn, hf, hwords,
    ⟨t, ht.trans (sourceBudget_le r Q Δ D scopes
      (Nat.pos_of_ne_zero (NeZero.ne r)) hd), he⟩, ho, hready⟩

/-- The compiler contributes a fixed constant, since the assignment
instruction table has no input-size or field-parameter argument. -/
theorem primitive_run_polynomial (regs : Fin 16 → Bool) (r Q Δ D : ℕ) [NeZero r]
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q), ∃ e : AssignmentFrontendProgram.Data,
      (a :: tail).Nodup ∧ (∀ w, w ∈ a :: tail) ∧
      (a :: tail).map ReadPlan.encodeWord = AssignmentAlphabetSemantics.wordBytes r Q ∧
      Computation.RunsIn (primitive AssignmentFrontendProgram.program).step
        (primitiveOverhead AssignmentFrontendProgram.program *
          (coefficient * sourceSize r Q Δ D scopes ^ 60))
        (primitiveCfg AssignmentFrontendProgram.program
          ((AssignmentPairFrontend.inputState regs r Q Δ D scopes).withPC
            (some AssignmentFrontendProgram.program.entry)))
        (primitiveCfg AssignmentFrontendProgram.program (e.withPC none)) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues
        (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
        a tail (List.finRange D)
        (AssignmentEnumeration.seedIndices (List.finRange D)
          (List.finRange scopes.length) Δ)).reverse.map ReadPlan.encodeWord).flatten ∧
      AssignmentFrontendProgram.RuntimeReady
        (AssignmentInputProgram.context r Q Δ D scopes.length
          (AssignmentPairFrontend.pairBytes D Δ scopes)) e := by
  obtain ⟨a, tail, e, hn, hf, hwords, he, ho, hready⟩ :=
    program_run_polynomial regs r Q Δ D scopes hd
  exact ⟨a, tail, e, hn, hf, hwords, primitive_execution AssignmentFrontendProgram.program he,
    ho, hready⟩

end SubexponentialSAT.Subexp.AssignmentFrontendBounds

end OAI.Algorithms
