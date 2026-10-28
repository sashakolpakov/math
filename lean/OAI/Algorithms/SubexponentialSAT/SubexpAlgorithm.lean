import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Algorithm

namespace OAI.Algorithms

/-!
# Executable separation into a growing number of groups

Each outer block contains a list of independent inner lists. The program first
sums each inner list, then multiplies the resulting sums. It never enumerates
the Cartesian product of those inner lists. All operation formulas display the
number of colors; no fixed-color constant is hidden in them.
-/

namespace SubexponentialSAT.SubexpAlgorithm

open scoped BigOperators

abbrev Expr := Algorithm.Expr
abbrev WeightedTerm := Algorithm.WeightedTerm

universe u

/-- Explicit data for one choice of the outer coordinates and all cosets. -/
structure Block (R : Type u) where
  outside : R
  groups : List (List (WeightedTerm R))

def groupExpression {R : Type*} [Zero R] (terms : List (WeightedTerm R)) : Expr R :=
  Algorithm.Expr.sum (terms.map Algorithm.WeightedTerm.expression)

theorem groupExpression_eval {R : Type*} [Semiring R] (terms : List (WeightedTerm R)) :
    (groupExpression terms).eval =
      (terms.map fun t => t.weight * t.group.eval).sum := by
  simp [groupExpression, List.map_map, Function.comp_def]

theorem groupExpression_size {R : Type*} [Zero R] (terms : List (WeightedTerm R)) :
    (groupExpression terms).size =
      (terms.map fun t => t.group.size).sum + 3 * terms.length + 1 := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      change t.expression.size + (groupExpression ts).size + 1 = _
      rw [Algorithm.WeightedTerm.expression_size, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

namespace Block

variable {R : Type*}

/-- The r-fold product of independent sums in equation (4.6). -/
def expression [Zero R] [One R] (b : Block R) : Expr R :=
  .mul (.lit b.outside) (Algorithm.Expr.product (b.groups.map groupExpression))

def innerCalls (b : Block R) : ℕ := (b.groups.map List.length).sum

def groupInstructions (b : Block R) : ℕ :=
  (b.groups.map fun ts => (ts.map fun t => t.group.size).sum).sum

@[simp] theorem expression_eval [Semiring R] (b : Block R) :
    b.expression.eval = b.outside *
      (b.groups.map fun ts => (ts.map fun t => t.weight * t.group.eval).sum).prod := by
  simp [expression, Algorithm.Expr.eval, groupExpression_eval,
    List.map_map, Function.comp_def]

private theorem productGroups_size [Zero R] [One R]
    (groups : List (List (WeightedTerm R))) :
    (Algorithm.Expr.product (groups.map groupExpression)).size =
      (groups.map fun ts => (ts.map fun t => t.group.size).sum).sum +
        3 * (groups.map List.length).sum + 2 * groups.length + 1 := by
  induction groups with
  | nil => rfl
  | cons ts rest ih =>
      simp only [List.map_cons, Algorithm.Expr.product, Algorithm.Expr.size,
        groupExpression_size, ih, List.sum_cons, List.length_cons]
      omega

/-- Every group computation is charged, and inner lengths occur only as a sum. -/
theorem expression_size [Zero R] [One R] (b : Block R) :
    b.expression.size = b.groupInstructions + 3 * b.innerCalls + 2 * b.groups.length + 3 := by
  simp only [expression, Algorithm.Expr.size, productGroups_size,
    groupInstructions, innerCalls]
  omega

/-- Construct a block from an actual Fin r family of inner enumeration lists. -/
def ofFibers {r : ℕ} {X : Fin r → Type*} (c : R)
    (xs : ∀ g, List (X g)) (weight : ∀ g, X g → R)
    (group : ∀ g, X g → Expr R) : Block R :=
  ⟨c, List.ofFn fun g => (xs g).map fun x => ⟨weight g x, group g x⟩⟩

@[simp] theorem ofFibers_colors {r : ℕ} {X : Fin r → Type*} (c : R)
    (xs : ∀ g, List (X g)) (weight : ∀ g, X g → R) (group : ∀ g, X g → Expr R) :
    (ofFibers c xs weight group).groups.length = r := by simp [ofFibers]

theorem ofFibers_innerCalls {r : ℕ} {X : Fin r → Type*} (c : R)
    (xs : ∀ g, List (X g)) (weight : ∀ g, X g → R) (group : ∀ g, X g → Expr R) :
    (ofFibers c xs weight group).innerCalls = ∑ g, (xs g).length := by
  simp [innerCalls, ofFibers, List.map_ofFn, List.sum_ofFn]

theorem ofFibers_eval [CommSemiring R] {r : ℕ} {X : Fin r → Type*} (c : R)
    (xs : ∀ g, List (X g)) (weight : ∀ g, X g → R) (group : ∀ g, X g → Expr R) :
    (ofFibers c xs weight group).expression.eval =
      c * ∏ g, ((xs g).map fun x => weight g x * (group g x).eval).sum := by
  simp [expression_eval, ofFibers, List.map_ofFn, List.prod_ofFn,
    List.map_map, Function.comp_def]

end Block

def momentExpression {R : Type*} [Zero R] [One R] (blocks : List (Block R)) : Expr R :=
  Algorithm.Expr.sum (blocks.map Block.expression)

theorem momentExpression_eval {R : Type*} [Semiring R] (blocks : List (Block R)) :
    (momentExpression blocks).eval =
      (blocks.map fun b => b.outside *
        (b.groups.map fun ts => (ts.map fun t => t.weight * t.group.eval).sum).prod).sum := by
  simp [momentExpression, List.map_map, Function.comp_def]

theorem momentExpression_size {R : Type*} [Zero R] [One R] (blocks : List (Block R)) :
    (momentExpression blocks).size =
      (blocks.map Block.groupInstructions).sum + 3 * (blocks.map Block.innerCalls).sum +
        2 * (blocks.map fun b => b.groups.length).sum + 4 * blocks.length + 1 := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
      change b.expression.size + (momentExpression bs).size + 1 = _
      rw [Block.expression_size, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

private theorem term_sizes_le {R : Type*} (terms : List (WeightedTerm R)) (S : ℕ)
    (h : ∀ t ∈ terms, t.group.size ≤ S) :
    (terms.map fun t => t.group.size).sum ≤ S * terms.length := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
      have ht := h t (by simp)
      have hs := ih (fun u hu => h u (by simp [hu]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem Block.groupInstructions_le {R : Type*} (b : Block R) (S : ℕ)
    (h : ∀ ts ∈ b.groups, ∀ t ∈ ts, t.group.size ≤ S) :
    b.groupInstructions ≤ S * b.innerCalls := by
  calc
    _ ≤ (b.groups.map fun ts => S * ts.length).sum :=
      List.sum_le_sum (fun ts hts => term_sizes_le ts S (h ts hts))
    _ = _ := List.sum_map_mul_left _ _ _

/-- A uniform bound in the number of colors, outer blocks and inner terms.
The group-program bound S is not permitted to hide a dependence on r. -/
theorem momentExpression_size_le {R : Type*} [Zero R] [One R]
    (blocks : List (Block R)) (S r : ℕ)
    (hs : ∀ b ∈ blocks, ∀ ts ∈ b.groups, ∀ t ∈ ts, t.group.size ≤ S)
    (hr : ∀ b ∈ blocks, b.groups.length ≤ r) :
    (momentExpression blocks).size ≤
      (S + 3) * (blocks.map Block.innerCalls).sum + (2 * r + 4) * blocks.length + 1 := by
  have hg : (blocks.map Block.groupInstructions).sum ≤
      S * (blocks.map Block.innerCalls).sum := by
    calc
      _ ≤ (blocks.map fun b => S * b.innerCalls).sum :=
        List.sum_le_sum (fun b hb => b.groupInstructions_le S (hs b hb))
      _ = _ := List.sum_map_mul_left _ _ _
  have hc : (blocks.map fun b => b.groups.length).sum ≤ r * blocks.length := by
    have h := List.sum_le_sum hr
    simpa [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm] using h
  rw [momentExpression_size]
  calc
    _ ≤ S * (blocks.map Block.innerCalls).sum + 3 * (blocks.map Block.innerCalls).sum +
        2 * (r * blocks.length) + 4 * blocks.length + 1 := by omega
    _ = _ := by ring

/-- An actual arithmetic-machine execution of the complete r-group moment. -/
theorem momentExpression_trace {R : Type*} [Zero R] [One R] [Add R] [Mul R]
    (blocks : List (Block R)) :
    Computation.Trace Algorithm.step
      ((blocks.map Block.groupInstructions).sum + 3 * (blocks.map Block.innerCalls).sum +
        2 * (blocks.map fun b => b.groups.length).sum + 4 * blocks.length + 1)
      ⟨(momentExpression blocks).compile, []⟩ ⟨[], [(momentExpression blocks).eval]⟩ := by
  rw [← momentExpression_size]
  simpa using (momentExpression blocks).compile_trace [] []

private theorem map_product {R S : Type*} [One R] [One S]
    (f : R → S) (hf : f 1 = 1) (es : List (Expr R)) :
    (Algorithm.Expr.product es).map f =
      Algorithm.Expr.product (es.map fun e => e.map f) := by
  induction es with
  | nil => simp [Algorithm.Expr.product, Algorithm.Expr.map, hf]
  | cons e es ih => simp [Algorithm.Expr.product, Algorithm.Expr.map, ih]

namespace Block

def map {R S : Type*} (f : R → S) (b : Block R) : Block S :=
  ⟨f b.outside, b.groups.map fun ts => ts.map (Algorithm.WeightedTerm.map f)⟩

theorem map_expression {R S : Type*} [Zero R] [One R] [Zero S] [One S]
    (f : R → S) (h0 : f 0 = 0) (h1 : f 1 = 1) (b : Block R) :
    b.expression.map f = (b.map f).expression := by
  simp [expression, groupExpression, Algorithm.Expr.map, map_product f h1,
    Algorithm.Expr.map_sum f h0, map, Algorithm.WeightedTerm.map_expression,
    List.map_map, Function.comp_def]

end Block

theorem map_momentExpression {R S : Type*} [Zero R] [One R] [Zero S] [One S]
    (f : R → S) (h0 : f 0 = 0) (h1 : f 1 = 1) (blocks : List (Block R)) :
    (momentExpression blocks).map f = momentExpression (blocks.map (Block.map f)) := by
  simp [momentExpression, Algorithm.Expr.map_sum f h0, Block.map_expression f h0 h1,
    List.map_map, Function.comp_def]

def rawOne (D : ℕ) {R : Type*} [One R] : SymbolicCost.CoeffList D R :=
  [(((fun _ => 0), (0, 0)), 1)]

theorem rawOne_denote (D : ℕ) {R : Type*} [CommSemiring R] :
    SymbolicCost.denote (rawOne D : SymbolicCost.CoeffList D R) = 1 := by
  have hz : (Finsupp.equivFunOnFinite.symm (fun _ : Fin D => 0) : Fin D →₀ ℕ) = 0 := by
    ext i
    rfl
  simp [rawOne, SymbolicCost.denote, SymbolicCost.monomial, hz]

def rawMomentExpression {D : ℕ} {R : Type*} [One R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) : Expr (SymbolicCost.CoeffList D R) :=
  letI : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  letI : One (SymbolicCost.CoeffList D R) := ⟨rawOne D⟩
  momentExpression blocks

theorem rawMomentExpression_size {D : ℕ} {R : Type*} [One R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    (rawMomentExpression blocks).size =
      (blocks.map Block.groupInstructions).sum + 3 * (blocks.map Block.innerCalls).sum +
        2 * (blocks.map fun b => b.groups.length).sum + 4 * blocks.length + 1 := by
  let _ : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  let _ : One (SymbolicCost.CoeffList D R) := ⟨rawOne D⟩
  exact momentExpression_size blocks

noncomputable def rawMomentValue {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) : SymbolicCost.Poly D R :=
  (blocks.map fun b => SymbolicCost.denote b.outside *
    (b.groups.map fun ts => (ts.map fun t => SymbolicCost.denote t.weight *
      (t.group.map SymbolicCost.denote).eval).sum).prod).sum

theorem rawMomentExpression_value {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    ((rawMomentExpression blocks).map SymbolicCost.denote).eval = rawMomentValue blocks := by
  let _ : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  let _ : One (SymbolicCost.CoeffList D R) := ⟨rawOne D⟩
  change ((momentExpression blocks).map SymbolicCost.denote).eval = _
  rw [map_momentExpression SymbolicCost.denote (by rfl) (rawOne_denote D),
    momentExpression_eval]
  simp [rawMomentValue, Block.map, Algorithm.WeightedTerm.map,
    List.map_map, Function.comp_def]

/-- A finite r-group coefficient-list algorithm. The same monomial enumeration,
bounded postfix execution, and post-extraction U summation work for every r. -/
def executeJet {D : ℕ} {R : Type*} [Semiring R]
    (blocks : (Fin D → ℕ) → List (Block (SymbolicCost.CoeffList D R))) : List R :=
  Algorithm.executeRawJet (fun a => rawMomentExpression (blocks a))

theorem executeJet_eq {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : (Fin D → ℕ) → List (Block (SymbolicCost.CoeffList D R))) :
    executeJet blocks = (List.range D).map fun r =>
      ((Algorithm.exponentList D (2 * D + 1)).map fun a =>
        (Algorithm.extractPolynomial (Finsupp.equivFunOnFinite.symm a)
          (Truncation.canonical (D + 1) D (2 * D + 1)
            (rawMomentValue (blocks a)))).coeff r).sum := by
  rw [executeJet, Algorithm.executeRawJet_eq]
  simp only [rawMomentExpression_value]

theorem dense_cost {D : ℕ} {R : Type*} [Semiring R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    ((rawMomentExpression blocks).map
      (Algorithm.Dense.ofRaw (Algorithm.retainedSlots D))).cost
      (Algorithm.Dense.costs (Algorithm.retainedSlots D)) ≤
      Algorithm.Dense.instructionBudget (Algorithm.retainedSlots D) *
        ((blocks.map Block.groupInstructions).sum + 3 * (blocks.map Block.innerCalls).sum +
          2 * (blocks.map fun b => b.groups.length).sum + 4 * blocks.length + 1) := by
  simpa only [Algorithm.Expr.size_map, rawMomentExpression_size] using
    Algorithm.denseExpression_cost_le (Algorithm.retainedSlots D)
      ((rawMomentExpression blocks).map (Algorithm.Dense.ofRaw (Algorithm.retainedSlots D)))

end SubexponentialSAT.SubexpAlgorithm

end OAI.Algorithms
