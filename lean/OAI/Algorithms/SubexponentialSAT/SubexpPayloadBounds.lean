import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramBuilder
import OAI.Algorithms.SubexponentialSAT.SubexpExecution

namespace OAI.Algorithms

/-!
# Literal payload bounds for the generated separated program

The bound counts entries of raw coefficient lists. Scalar weights and table
coefficients have one entry, zero has none, and each marked Taylor argument
has exactly `2 + (q + 1) * D` entries. The syntax constructors preserve this
bound without restrictions on the number of factors or table rows.

This is a structural input-size theorem for the measured evaluator. It makes
no claim about the bit cost of constructing or loading a list entry.
-/

namespace SubexponentialSAT.SubexpPayloadBounds

open SubexpExecution

section Syntax

variable {L R : Type*}

theorem everyLiteral_sum [Zero L] (P : L → Prop) (h0 : P 0)
    (es : List (Algorithm.Expr L)) (he : ∀ e ∈ es, EveryLiteral P e) :
    EveryLiteral P (Algorithm.Expr.sum es) := by
  induction es with
  | nil => exact h0
  | cons e es ih =>
      exact ⟨he e (by simp), ih (fun f hf => he f (by simp [hf]))⟩

theorem everyLiteral_product [One L] (P : L → Prop) (h1 : P 1)
    (es : List (Algorithm.Expr L)) (he : ∀ e ∈ es, EveryLiteral P e) :
    EveryLiteral P (Algorithm.Expr.product es) := by
  induction es with
  | nil => exact h1
  | cons e es ih =>
      exact ⟨he e (by simp), ih (fun f hf => he f (by simp [hf]))⟩

theorem everyLiteral_hornerExpr [Zero L] (P : L → Prop) (h0 : P 0)
    (literal : R → L) (hl : ∀ a, P (literal a))
    (x : Algorithm.Expr L) (hx : EveryLiteral P x) (coefficients : List R) :
    EveryLiteral P (SubexpTableInterpolation.hornerExpr literal x coefficients) := by
  induction coefficients with
  | nil => exact h0
  | cons a as ih => exact ⟨hl a, hx, ih⟩

theorem everyLiteral_rowExpr [Zero L] [One L] {p k : ℕ}
    (P : L → Prop) (h0 : P 0) (h1 : P 1)
    (literal : R → L) (hl : ∀ a, P (literal a)) (cache : List (List R))
    (row : SubexpTableInterpolation.Row p k R) (inputs : Fin k → Algorithm.Expr L)
    (hi : ∀ i, EveryLiteral P (inputs i)) :
    EveryLiteral P (SubexpTableInterpolation.rowExpr literal cache row inputs) := by
  refine ⟨hl row.value, everyLiteral_product P h1 _ ?_⟩
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact everyLiteral_hornerExpr P h0 literal hl (inputs i) (hi i) _

theorem everyLiteral_tableExpr [Zero L] [One L] {p k : ℕ}
    (P : L → Prop) (h0 : P 0) (h1 : P 1)
    (literal : R → L) (hl : ∀ a, P (literal a)) (cache : List (List R))
    (rows : List (SubexpTableInterpolation.Row p k R)) (inputs : Fin k → Algorithm.Expr L)
    (hi : ∀ i, EveryLiteral P (inputs i)) :
    EveryLiteral P (SubexpTableInterpolation.tableExpr literal cache rows inputs) := by
  apply everyLiteral_sum P h0
  intro e he
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp he
  exact everyLiteral_rowExpr P h0 h1 literal hl cache row inputs hi

/-- Literal obligations carried by a block before its expression is assembled. -/
def BlockLiterals (P : L → Prop) (b : SubexpAlgorithm.Block L) : Prop :=
  P b.outside ∧ ∀ terms ∈ b.groups, ∀ term ∈ terms,
    P term.weight ∧ EveryLiteral P term.group

theorem everyLiteral_groupExpression [Zero L] (P : L → Prop) (h0 : P 0)
    (terms : List (Algorithm.WeightedTerm L))
    (ht : ∀ term ∈ terms, P term.weight ∧ EveryLiteral P term.group) :
    EveryLiteral P (SubexpAlgorithm.groupExpression terms) := by
  apply everyLiteral_sum P h0
  intro e he
  obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp he
  exact ht term hterm

theorem everyLiteral_blockExpression [Zero L] [One L]
    (P : L → Prop) (h0 : P 0) (h1 : P 1) (b : SubexpAlgorithm.Block L)
    (hb : BlockLiterals P b) : EveryLiteral P b.expression := by
  refine ⟨hb.1, everyLiteral_product P h1 _ ?_⟩
  intro e he
  obtain ⟨terms, hterms, rfl⟩ := List.mem_map.mp he
  exact everyLiteral_groupExpression P h0 terms (hb.2 terms hterms)

theorem everyLiteral_momentExpression [Zero L] [One L]
    (P : L → Prop) (h0 : P 0) (h1 : P 1) (blocks : List (SubexpAlgorithm.Block L))
    (hb : ∀ b ∈ blocks, BlockLiterals P b) :
    EveryLiteral P (SubexpAlgorithm.momentExpression blocks) := by
  apply everyLiteral_sum P h0
  intro e he
  obtain ⟨b, hblock, rfl⟩ := List.mem_map.mp he
  exact everyLiteral_blockExpression P h0 h1 b (hb b hblock)

end Syntax

section Generated

open SubexpProgramBuilder

variable {D p q r : ℕ} {K A F : Type*}

theorem factorExpr_everyLiteral [Zero K] [Add K] [Mul K] [One A] [Neg A]
    (lift : K → A) (cache : List (List A))
    (f : FactorData D p q r K A) (x : Fin D → K) :
    EveryLiteral (fun raw => raw.length ≤ 2 + (q + 1) * D)
      (factorExpr lift cache f x) := by
  let : Zero (Raw D A) := ⟨[]⟩
  let : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  apply everyLiteral_tableExpr
  · change 0 ≤ _
    omega
  · change (SubexpAlgorithm.rawOne D : Raw D A).length ≤ _
    simp [SubexpAlgorithm.rawOne]
    omega
  · intro a
    simp [SubexpWeightCode.rawScalar]
    omega
  · intro i
    change (argument lift f x i).length ≤ _
    simp

theorem groupExpr_everyLiteral [Zero K] [Add K] [Mul K] [One A] [Neg A]
    (lift : K → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A)) (g : Fin r) (x : Fin D → K) :
    EveryLiteral (fun raw => raw.length ≤ 2 + (q + 1) * D)
      (groupExpr lift cache factors g x) := by
  let : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  apply everyLiteral_product
  · change (SubexpAlgorithm.rawOne D : Raw D A).length ≤ _
    simp [SubexpAlgorithm.rawOne]
    omega
  · intro e he
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
    exact factorExpr_everyLiteral lift cache f x

theorem block_literals [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (base : Fin D → F) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    BlockLiterals (fun raw => raw.length ≤ 2 + (q + 1) * D)
      (block embed betaLift weightLift cache factors supports outside base increments a) := by
  constructor
  · change (SubexpWeightCode.rawWeightWithCost _ _ _).1.length ≤ _
    simp
    omega
  · intro terms hterms term hterm
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hterms
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hterm
    constructor
    · change (SubexpWeightCode.rawWeightWithCost _ _ _).1.length ≤ _
      simp
      omega
    · exact groupExpr_everyLiteral betaLift cache factors g _

/-- Every literal in the actual generated raw moment program satisfies the
load-size bound used by `SubexpExecution.programEval_cost`. -/
theorem blocks_everyLiteral [Add F] [Zero K] [Add K] [Mul K] [One A] [Mul A] [Neg A]
    (embed : F → K) (betaLift : K → A) (weightLift : F → A) (cache : List (List A))
    (factors : List (FactorData D p q r K A))
    (supports : Fin r → List (Fin D)) (outside : List (Fin D))
    (bases : List (Fin D → F)) (increments : Fin r → List (Fin D → F)) (a : Fin D → ℕ) :
    EveryLiteral (fun raw => raw.length ≤ 2 + (q + 1) * D)
      (SubexpAlgorithm.rawMomentExpression
        (blocks embed betaLift weightLift cache factors supports outside bases increments a)) := by
  let : Zero (Raw D A) := ⟨[]⟩
  let : One (Raw D A) := ⟨SubexpAlgorithm.rawOne D⟩
  apply everyLiteral_momentExpression
  · change 0 ≤ _
    omega
  · change (SubexpAlgorithm.rawOne D : Raw D A).length ≤ _
    simp [SubexpAlgorithm.rawOne]
    omega
  · intro b hb
    obtain ⟨base, _, rfl⟩ := List.mem_map.mp hb
    exact block_literals embed betaLift weightLift cache factors supports outside base increments a

end Generated

end SubexponentialSAT.SubexpPayloadBounds

end OAI.Algorithms
