import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.Moments
import OAI.Algorithms.SubexponentialSAT.Separation
import OAI.Algorithms.SubexponentialSAT.JetCRT
import OAI.Algorithms.SubexponentialSAT.SymbolicCost

namespace OAI.Algorithms

/-!
# Executable separated arithmetic kernels

The arithmetic expressions and their postfix compiler in this file are data.
The evaluator contains no choice, no decision of a semantic proposition, and no
enumeration of the Cartesian product of the two inner lists.  Its instruction
counts are proved by actual transition traces.  An arithmetic instruction is
not a primitive bit-machine instruction: refining the supplied coefficient
operations to the latter remains a separate obligation.
-/

namespace SubexponentialSAT.Algorithm

open scoped BigOperators

universe u

/-- Finite syntax for computations in the retained coefficient algebra. -/
inductive Expr (R : Type u) where
  | lit : R → Expr R
  | add : Expr R → Expr R → Expr R
  | mul : Expr R → Expr R → Expr R

namespace Expr

variable {R : Type u}

/-- Structural evaluation using the supplied, executable coefficient operations. -/
def eval [Add R] [Mul R] : Expr R → R
  | .lit x => x
  | .add e f => eval e + eval f
  | .mul e f => eval e * eval f

/-- Number of postfix instructions, including explicit coefficient loads. -/
def size : Expr R → ℕ
  | .lit _ => 1
  | .add e f => size e + size f + 1
  | .mul e f => size e + size f + 1

/-- A finite summation program. Its syntax contains each input exactly once. -/
def sum [Zero R] : List (Expr R) → Expr R
  | [] => .lit 0
  | e :: es => .add e (sum es)

/-- A finite group product; all factor computations remain explicit syntax. -/
def product [One R] : List (Expr R) → Expr R
  | [] => .lit 1
  | e :: es => .mul e (product es)

@[simp] theorem eval_sum [AddMonoid R] [Mul R] (es : List (Expr R)) :
    (sum es).eval = (es.map eval).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sum, eval, ih]

theorem size_sum [Zero R] (es : List (Expr R)) :
    (sum es).size = (es.map size).sum + es.length + 1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [sum, size, ih, List.map_cons, List.sum_cons,
      List.length_cons]; omega

@[simp] theorem eval_product [Monoid R] [Add R] (es : List (Expr R)) :
    (product es).eval = (es.map eval).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [product, eval, ih]

theorem size_product [One R] (es : List (Expr R)) :
    (product es).size = (es.map size).sum + es.length + 1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [product, size, ih, List.map_cons, List.sum_cons,
      List.length_cons]; omega

/-- Multiplication by a natural power, built by a terminating finite loop. -/
def pow [One R] (e : Expr R) : ℕ → Expr R
  | 0 => .lit 1
  | n + 1 => .mul (pow e n) e

@[simp] theorem eval_pow [Monoid R] [Add R] (e : Expr R) (n : ℕ) :
    (pow e n).eval = e.eval ^ n := by
  induction n with
  | zero => simp [pow, eval]
  | succ n ih => simp [pow, eval, ih, pow_succ]

theorem size_pow [One R] (e : Expr R) (n : ℕ) :
    (pow e n).size = n * (e.size + 1) + 1 := by
  induction n with
  | zero => simp [pow, size]
  | succ n ih => simp only [pow, size, ih, Nat.add_mul]; omega

/-- Change only coefficient representations, leaving the program unchanged. -/
def map {S : Type*} (f : R → S) : Expr R → Expr S
  | .lit r => .lit (f r)
  | .add e g => .add (e.map f) (g.map f)
  | .mul e g => .mul (e.map f) (g.map f)

@[simp] theorem size_map {S : Type*} (f : R → S) (e : Expr R) :
    (e.map f).size = e.size := by
  induction e with
  | lit => rfl
  | add e g he hg => simp [map, size, he, hg]
  | mul e g he hg => simp [map, size, he, hg]

/-- A proved implementation of the two coefficient operations transports
expression correctness. This does not assume a runtime for that implementation. -/
theorem eval_map {S : Type*} [Add R] [Mul R] [Add S] [Mul S]
    (f : R → S) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmul : ∀ x y, f (x * y) = f x * f y) (e : Expr R) :
    (e.map f).eval = f e.eval := by
  induction e with
  | lit => rfl
  | add e g he hg => simp [map, eval, he, hg, hadd]
  | mul e g he hg => simp [map, eval, he, hg, hmul]

end Expr

/-- A single explicitly stored term of a factor table polynomial. The list
contains its argument expressions together with their natural exponents. -/
structure TableTerm (R : Type u) where
  coefficient : R
  powers : List (Expr R × ℕ)

namespace TableTerm

variable {R : Type u}

def expression [One R] (t : TableTerm R) : Expr R :=
  .mul (.lit t.coefficient)
    (Expr.product (t.powers.map fun en => Expr.pow en.1 en.2))

@[simp] theorem expression_eval [Monoid R] [Add R] (t : TableTerm R) :
    t.expression.eval = t.coefficient *
      (t.powers.map fun en => en.1.eval ^ en.2).prod := by
  simp [expression, Expr.eval, List.map_map, Function.comp_def]

end TableTerm

/-- Compile a factor from its finite coefficient table, without expanding a
full untruncated multivariate polynomial. The supplied operations can themselves
be the clipped coefficient-list operations. -/
def tableExpression {R : Type u} [Zero R] [One R]
    (terms : List (TableTerm R)) : Expr R :=
  Expr.sum (terms.map TableTerm.expression)

theorem tableExpression_eval {R : Type u} [Semiring R]
    (terms : List (TableTerm R)) :
    (tableExpression terms).eval =
      (terms.map fun t => t.coefficient *
        (t.powers.map fun en => en.1.eval ^ en.2).prod).sum := by
  simp [tableExpression, List.map_map, Function.comp_def]

/-- The three actual instructions of the arithmetic kernel. -/
inductive Instr (R : Type u) where
  | push : R → Instr R
  | add : Instr R
  | mul : Instr R

/-- Explicit remaining code and an explicit operand stack. -/
structure State (R : Type u) where
  code : List (Instr R)
  stack : List R

/-- One arithmetic-machine transition. Malformed programs stop on underflow. -/
def step {R : Type u} [Add R] [Mul R] : State R → Option (State R)
  | ⟨[], _⟩ => none
  | ⟨.push x :: is, xs⟩ => some ⟨is, x :: xs⟩
  | ⟨.add :: is, y :: x :: xs⟩ => some ⟨is, (x + y) :: xs⟩
  | ⟨.mul :: is, y :: x :: xs⟩ => some ⟨is, (x * y) :: xs⟩
  | _ => none

/-- Proposed costs for the three concrete operations. They acquire a machine
interpretation only through a measured simulation of the corresponding step. -/
structure OperationCosts (R : Type u) where
  load : R → ℕ
  add : R → R → ℕ
  mul : R → R → ℕ

def instructionCost {R : Type u} (costs : OperationCosts R) : State R → ℕ
  | ⟨.push x :: _, _⟩ => costs.load x
  | ⟨.add :: _, y :: x :: _⟩ => costs.add x y
  | ⟨.mul :: _, y :: x :: _⟩ => costs.mul x y
  | _ => 0

private theorem costedTrace_trans {α : Type*} {next : α → Option α}
    {cost : α → ℕ} {n m : ℕ} {a b c : α}
    (h₁ : Computation.CostedTrace next cost n a b)
    (h₂ : Computation.CostedTrace next cost m b c) :
    Computation.CostedTrace next cost (n + m) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | cons hs ht ih => simpa [Nat.add_assoc] using Computation.CostedTrace.cons hs (ih h₂)

namespace Expr

variable {R : Type u}

/-- Postfix compilation is structural and contains no interpreter oracle. -/
def compile : Expr R → List (Instr R)
  | .lit x => [.push x]
  | .add e f => compile e ++ compile f ++ [.add]
  | .mul e f => compile e ++ compile f ++ [.mul]

/-- The costs of the actually encountered operands, not worst-case guesses. -/
def cost [Add R] [Mul R] (costs : OperationCosts R) : Expr R → ℕ
  | .lit x => costs.load x
  | .add e f => cost costs e + cost costs f + costs.add e.eval f.eval
  | .mul e f => cost costs e + cost costs f + costs.mul e.eval f.eval

@[simp] theorem length_compile (e : Expr R) : e.compile.length = e.size := by
  induction e with
  | lit => rfl
  | add e f he hf => simp [compile, size, he, hf, Nat.add_assoc]
  | mul e f he hf => simp [compile, size, he, hf, Nat.add_assoc]

/-- Every compiled expression executes without underflow, including in a larger
program. The bound is an actual trace length, not an assigned cost annotation. -/
theorem compile_trace [Add R] [Mul R] (e : Expr R)
    (suffix : List (Instr R)) (stack : List R) :
    Computation.Trace step e.size
      ⟨e.compile ++ suffix, stack⟩ ⟨suffix, e.eval :: stack⟩ := by
  induction e generalizing suffix stack with
  | lit x => exact Computation.Trace.cons rfl (.refl _)
  | add e f he hf =>
      have h₁ := he (f.compile ++ .add :: suffix) stack
      have h₂ := hf (.add :: suffix) (e.eval :: stack)
      have h₃ : Computation.Trace step 1
          (⟨.add :: suffix, f.eval :: e.eval :: stack⟩ : State R)
          ⟨suffix, (e.eval + f.eval) :: stack⟩ :=
        .cons rfl (.refl _)
      simpa [compile, size, eval, List.append_assoc] using (h₁.trans h₂).trans h₃
  | mul e f he hf =>
      have h₁ := he (f.compile ++ .mul :: suffix) stack
      have h₂ := hf (.mul :: suffix) (e.eval :: stack)
      have h₃ : Computation.Trace step 1
          (⟨.mul :: suffix, f.eval :: e.eval :: stack⟩ : State R)
          ⟨suffix, (e.eval * f.eval) :: stack⟩ :=
        .cons rfl (.refl _)
      simpa [compile, size, eval, List.append_assoc] using (h₁.trans h₂).trans h₃

theorem compile_halts [Add R] [Mul R] (e : Expr R) :
    Computation.RunsIn step e.size
      ⟨e.compile, []⟩ ⟨[], [e.eval]⟩ := by
  exact ⟨e.size, le_rfl, by simpa using e.compile_trace [] []⟩

/-- A bounded executable run of the compiled code. Its fuel is derived from
the program syntax and the result contains the actual final machine state. -/
def run [Add R] [Mul R] (e : Expr R) : Option (State R) :=
  (fun s : Option (State R) => s.bind step)^[e.size]
    (some ⟨e.compile, []⟩)

@[simp] theorem run_eq [Add R] [Mul R] (e : Expr R) :
    e.run = some ⟨[], [e.eval]⟩ := by
  exact (show Computation.Trace step e.size
    (⟨e.compile, []⟩ : State R) ⟨[], [e.eval]⟩ from by
      simpa using e.compile_trace [] []).iterate

/-- Extract the result of the actual bounded postfix-machine run. The default
branch makes the function total and is proved unreachable for compiled code. -/
def execute [Zero R] [Add R] [Mul R] (e : Expr R) : R :=
  match e.run with
  | some ⟨[], [x]⟩ => x
  | _ => 0

@[simp] theorem execute_eq [Zero R] [Add R] [Mul R] (e : Expr R) :
    e.execute = e.eval := by
  simp [execute]

/-- Data-dependent operation costs are attached to the same actual execution. -/
theorem compile_costedTrace [Add R] [Mul R] (costs : OperationCosts R)
    (e : Expr R) (suffix : List (Instr R)) (stack : List R) :
    Computation.CostedTrace step (instructionCost costs) (e.cost costs)
      ⟨e.compile ++ suffix, stack⟩ ⟨suffix, e.eval :: stack⟩ := by
  induction e generalizing suffix stack with
  | lit x =>
      simpa [compile, cost, instructionCost, eval] using
        (Computation.CostedTrace.cons (source := step)
          (cost := instructionCost costs)
          (a := (⟨.push x :: suffix, stack⟩ : State R)) rfl
          (Computation.CostedTrace.refl (⟨suffix, x :: stack⟩ : State R)))
  | add e f he hf =>
      have h₁ := he (f.compile ++ .add :: suffix) stack
      have h₂ := hf (.add :: suffix) (e.eval :: stack)
      have h₃ : Computation.CostedTrace step (instructionCost costs)
          (costs.add e.eval f.eval)
          (⟨.add :: suffix, f.eval :: e.eval :: stack⟩ : State R)
          ⟨suffix, (e.eval + f.eval) :: stack⟩ := by
        simpa [instructionCost] using
          (Computation.CostedTrace.cons (source := step)
            (cost := instructionCost costs)
            (a := (⟨.add :: suffix, f.eval :: e.eval :: stack⟩ : State R)) rfl
            (Computation.CostedTrace.refl
              (⟨suffix, (e.eval + f.eval) :: stack⟩ : State R)))
      simpa [compile, cost, eval, List.append_assoc] using
        costedTrace_trans (costedTrace_trans h₁ h₂) h₃
  | mul e f he hf =>
      have h₁ := he (f.compile ++ .mul :: suffix) stack
      have h₂ := hf (.mul :: suffix) (e.eval :: stack)
      have h₃ : Computation.CostedTrace step (instructionCost costs)
          (costs.mul e.eval f.eval)
          (⟨.mul :: suffix, f.eval :: e.eval :: stack⟩ : State R)
          ⟨suffix, (e.eval * f.eval) :: stack⟩ := by
        simpa [instructionCost] using
          (Computation.CostedTrace.cons (source := step)
            (cost := instructionCost costs)
            (a := (⟨.mul :: suffix, f.eval :: e.eval :: stack⟩ : State R)) rfl
            (Computation.CostedTrace.refl
              (⟨suffix, (e.eval * f.eval) :: stack⟩ : State R)))
      simpa [compile, cost, eval, List.append_assoc] using
        costedTrace_trans (costedTrace_trans h₁ h₂) h₃

/-- An actual local bit-level implementation, when supplied, yields an actual
target execution. The local simulation premise cannot be replaced by a cost
annotation or by semantic equality of the final answers. -/
theorem runs_target_of_local_simulation [Add R] [Mul R]
    (costs : OperationCosts R) (e : Expr R) {B : Type*}
    (target : B → Option B) (related : State R → B → Prop)
    (sim : ∀ ⦃a a' b⦄, related a b → step a = some a' →
      ∃ b', related a' b' ∧ Computation.RunsIn target (instructionCost costs a) b b')
    (initial : B) (hinit : related ⟨e.compile, []⟩ initial) :
    ∃ final, related ⟨[], [e.eval]⟩ final ∧
      Computation.RunsIn target (e.cost costs) initial final := by
  apply Computation.simulate_costedTrace sim
    (show Computation.CostedTrace step (instructionCost costs) (e.cost costs)
      ⟨e.compile, []⟩ ⟨[], [e.eval]⟩ from by simpa using e.compile_costedTrace costs [] [])
    hinit

end Expr

/-- Execute every moment program in order. Each program is present exactly once. -/
def compileMany {R : Type*} : List (Expr R) → List (Instr R)
  | [] => []
  | e :: es => e.compile ++ compileMany es

theorem compileMany_trace {R : Type*} [Add R] [Mul R]
    (es : List (Expr R)) (suffix : List (Instr R)) (stack : List R) :
    Computation.Trace step (es.map Expr.size).sum
      ⟨compileMany es ++ suffix, stack⟩
      ⟨suffix, (es.map Expr.eval).reverse ++ stack⟩ := by
  induction es generalizing stack with
  | nil => exact .refl _
  | cons e es ih =>
      have h₁ := e.compile_trace (compileMany es ++ suffix) stack
      have h₂ := ih (e.eval :: stack)
      simpa [compileMany, List.append_assoc] using h₁.trans h₂

/-! ## Constructive output-sensitive monomial enumeration -/

/-- Enumerate nonnegative exponent vectors by spending the remaining degree
budget. Unlike the coordinate-box construction, this visits no rejected vector. -/
def exponentList : (D N : ℕ) → List (Fin D → ℕ)
  | 0, _ => [fun i => Fin.elim0 i]
  | D + 1, N => (List.range (N + 1)).flatMap fun a =>
      (exponentList D (N - a)).map (Fin.cons a)

theorem mem_exponentList (D N : ℕ) (a : Fin D → ℕ) :
    a ∈ exponentList D N ↔ ∑ i, a i ≤ N := by
  induction D generalizing N with
  | zero =>
      have ha : a = (fun i : Fin 0 => Fin.elim0 i) := funext fun i => Fin.elim0 i
      simp [exponentList, ha]
  | succ D ih =>
      simp only [exponentList, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨b, hb, c, hc, rfl⟩
        have hc' := (ih (N - b) c).mp hc
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        omega
      · intro ha
        have hsum : a 0 + ∑ i : Fin D, a i.succ ≤ N := by
          simpa only [Fin.sum_univ_succ] using ha
        refine ⟨a 0, by omega, (fun i => a i.succ),
          (ih (N - a 0) (fun i => a i.succ)).mpr (by omega), ?_⟩
        funext i
        exact Fin.cases rfl (fun _ => rfl) i

theorem exponentList_nodup (D N : ℕ) : (exponentList D N).Nodup := by
  induction D generalizing N with
  | zero => simp [exponentList]
  | succ D ih =>
      apply List.nodup_flatMap.mpr
      constructor
      · intro a ha
        exact (ih (N - a)).map (fun x y h => (Fin.cons_inj.mp h).2)
      · have hn : (List.range (N + 1)).Nodup := List.nodup_range
        apply hn.imp
        intro a b hab
        apply List.disjoint_left.mpr
        intro c hc hbc
        obtain ⟨x, hx, hxc⟩ := List.mem_map.mp hc
        obtain ⟨y, hy, hyc⟩ := List.mem_map.mp hbc
        exact hab (Fin.cons_inj.mp (hxc.trans hyc.symm)).1

/-- The list implements the actual bounded-exponent type counted by stars and bars. -/
def exponentListEquiv (D N : ℕ) :
    {a // a ∈ (exponentList D N).toFinset} ≃
      MonomialCount.BoundedExponents D N where
  toFun a := ⟨a.1, (mem_exponentList D N a.1).mp (List.mem_toFinset.mp a.2)⟩
  invFun a := ⟨a.1, List.mem_toFinset.mpr ((mem_exponentList D N a.1).mpr a.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem exponentList_length (D N : ℕ) :
    (exponentList D N).length = (D + N).choose D := by
  have h := Fintype.card_congr (exponentListEquiv D N)
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (exponentList_nodup D N),
    MonomialCount.card_boundedExponents] at h
  exact h

theorem exponentList_nonempty (D N : ℕ) : 0 < (exponentList D N).length := by
  have hmem : (fun _ : Fin D => 0) ∈ exponentList D N :=
    (mem_exponentList D N _).mpr (by simp)
  exact List.length_pos_of_mem hmem

/-- Recursive invocations made by the budget-spending enumeration. This counts
invocations, not list-cell or bit operations. -/
def exponentCalls : (D N : ℕ) → ℕ
  | 0, _ => 1
  | D + 1, N => 1 + ((List.range (N + 1)).map fun a => exponentCalls D (N - a)).sum

/-- The executable enumerator with its recursive-invocation count attached. -/
def exponentListWithCalls : (D N : ℕ) → List (Fin D → ℕ) × ℕ
  | 0, _ => ([fun i => Fin.elim0 i], 1)
  | D + 1, N =>
      let children := (List.range (N + 1)).map fun a => (a, exponentListWithCalls D (N - a))
      (children.flatMap (fun child => child.2.1.map (Fin.cons child.1)),
        1 + (children.map fun child => child.2.2).sum)

theorem exponentListWithCalls_eq (D N : ℕ) :
    exponentListWithCalls D N = (exponentList D N, exponentCalls D N) := by
  induction D generalizing N with
  | zero => rfl
  | succ D ih =>
      simp [exponentListWithCalls, ih, exponentList, exponentCalls,
        List.flatMap_map, List.map_map, Function.comp_def]

/-- The recursive search tree has at most D+1 invocations per output vector;
in particular the enumerator does not hide a full coordinate-box search. -/
theorem exponentCalls_le (D N : ℕ) :
    exponentCalls D N ≤ (D + 1) * (exponentList D N).length := by
  induction D generalizing N with
  | zero => simp [exponentCalls, exponentList]
  | succ D ih =>
      have hlen : ((List.range (N + 1)).map fun a =>
          (exponentList D (N - a)).length).sum = (exponentList (D + 1) N).length := by
        simp [exponentList, List.length_flatMap]
      have hsum : ((List.range (N + 1)).map fun a => exponentCalls D (N - a)).sum ≤
          (D + 1) * (exponentList (D + 1) N).length := by
        calc
          _ ≤ ((List.range (N + 1)).map fun a =>
              (D + 1) * (exponentList D (N - a)).length).sum :=
            List.sum_le_sum (fun a _ => ih (N - a))
          _ = (D + 1) * ((List.range (N + 1)).map fun a =>
              (exponentList D (N - a)).length).sum :=
            List.sum_map_mul_left _ _ _
          _ = _ := by rw [hlen]
      have hpos := exponentList_nonempty (D + 1) N
      change 1 + _ ≤ (D + 1 + 1) * _
      rw [Nat.add_mul]
      omega

/-- The complete retained coefficient slots, with a concrete finite order. -/
def retainedSlots (D : ℕ) : List (SymbolicCost.RawIndex D) :=
  (exponentList D (2 * D + 1)).product
    ((List.range (D + 1)).product (List.range D))

theorem retainedSlots_nodup (D : ℕ) : (retainedSlots D).Nodup :=
  (exponentList_nodup D (2 * D + 1)).product
    (List.nodup_range.product List.nodup_range)

theorem mem_retainedSlots (D : ℕ) (a : SymbolicCost.RawIndex D) :
    a ∈ retainedSlots D ↔ SymbolicCost.Retained D a := by
  rcases a with ⟨a, j, r⟩
  simp [retainedSlots, SymbolicCost.Retained, mem_exponentList]

theorem retainedSlots_length (D : ℕ) :
    (retainedSlots D).length = (3 * D + 1).choose D * ((D + 1) * D) := by
  change ((exponentList D (2 * D + 1)) ×ˢ
    ((List.range (D + 1)) ×ˢ (List.range D))).length = _
  rw [List.length_product, List.length_product, List.length_range, List.length_range,
    exponentList_length]
  have he : D + (2 * D + 1) = 3 * D + 1 := by omega
  rw [he]

/-! ## Concrete dense coefficients and the arithmetic-machine backend -/

/-- A coefficient list with the fixed length of the retained-slot list. -/
structure Dense {D : ℕ} (slots : List (SymbolicCost.RawIndex D)) (R : Type*) where
  coefficients : SymbolicCost.CoeffList D R
  length_eq : coefficients.length = slots.length

namespace Dense

variable {D : ℕ} {R : Type*} [Semiring R]
variable (slots : List (SymbolicCost.RawIndex D))

/-- Projection is executable, and proves the fixed-length storage invariant. -/
def ofRaw (P : SymbolicCost.CoeffList D R) : Dense slots R :=
  ⟨SymbolicCost.project slots P, SymbolicCost.length_project slots P⟩

instance : Zero (Dense slots R) := ⟨ofRaw slots []⟩

instance : One (Dense slots R) :=
  ⟨ofRaw slots [(((fun _ => 0), (0, 0)), 1)]⟩

instance : Add (Dense slots R) := ⟨fun P Q =>
  ⟨SymbolicCost.denseAdd slots P.coefficients Q.coefficients,
    SymbolicCost.length_project slots _⟩⟩

instance : Mul (Dense slots R) := ⟨fun P Q =>
  ⟨SymbolicCost.denseMul slots P.coefficients Q.coefficients,
    SymbolicCost.length_project slots _⟩⟩

/-- These are exact counts of the instrumented coefficient-list operations,
and a list-cell load count. They are not primitive bit-operation counts. -/
def costs : OperationCosts (Dense slots R) where
  load _ := slots.length
  add _ _ := SymbolicCost.denseAddCost slots.length
  mul _ _ := SymbolicCost.denseCost slots.length

theorem measured_add (P Q : Dense slots R) :
    SymbolicCost.denseAddWithCost slots P.coefficients Q.coefficients =
      ((P + Q).coefficients, (costs slots).add P Q) :=
  SymbolicCost.denseAddWithCost_dense slots P.coefficients Q.coefficients
    P.length_eq Q.length_eq

theorem measured_mul (P Q : Dense slots R) :
    SymbolicCost.denseMulWithCost slots P.coefficients Q.coefficients =
      ((P * Q).coefficients, (costs slots).mul P Q) :=
  SymbolicCost.denseMulWithCost_dense slots P.coefficients Q.coefficients
    P.length_eq Q.length_eq

def instructionBudget : ℕ :=
  SymbolicCost.denseCost slots.length + SymbolicCost.denseAddCost slots.length + slots.length

theorem instructionBudget_le : instructionBudget slots ≤ 21 * (slots.length + 1) ^ 3 := by
  have hm := SymbolicCost.denseCost_le slots.length
  have ha := SymbolicCost.denseAddCost_le slots.length
  have hl : slots.length ≤ (slots.length + 1) ^ 3 :=
    (Nat.le_succ _).trans (Nat.le_pow (by decide))
  unfold instructionBudget
  omega

end Dense

namespace Expr

variable {R : Type*} [Add R] [Mul R]

theorem cost_le_size (costs : OperationCosts R) (budget : ℕ)
    (hload : ∀ x, costs.load x ≤ budget)
    (hadd : ∀ x y, costs.add x y ≤ budget)
    (hmul : ∀ x y, costs.mul x y ≤ budget) (e : Expr R) :
    e.cost costs ≤ budget * e.size := by
  induction e with
  | lit x => simpa [cost, size] using hload x
  | add e f he hf =>
      calc
        _ ≤ budget * e.size + budget * f.size + budget :=
          Nat.add_le_add (Nat.add_le_add he hf) (hadd _ _)
        _ = _ := by simp [size, Nat.mul_add]
  | mul e f he hf =>
      calc
        _ ≤ budget * e.size + budget * f.size + budget :=
          Nat.add_le_add (Nat.add_le_add he hf) (hmul _ _)
        _ = _ := by simp [size, Nat.mul_add]

end Expr

theorem denseExpression_cost_le {D : ℕ} {R : Type*} [Semiring R]
    (slots : List (SymbolicCost.RawIndex D)) (e : Expr (Dense slots R)) :
    e.cost (Dense.costs slots) ≤ Dense.instructionBudget slots * e.size := by
  apply e.cost_le_size
  all_goals intros; simp only [Dense.costs, Dense.instructionBudget]; omega

private theorem canonical_idempotent {ι R : Type*} [CommSemiring R]
    (μ D N : ℕ) (P : Truncation.Poly ι R) :
    Truncation.canonical μ D N (Truncation.canonical μ D N P) =
      Truncation.canonical μ D N P := by
  ext j r a
  by_cases hj : j < μ <;> by_cases hr : r < D <;>
    by_cases ha : a.sum (fun _ n => n) ≤ N <;>
    simp [Truncation.coeff_canonical, Truncation.coeff_xTrunc, hj, hr, ha]

private theorem denote_project {D : ℕ} {R : Type*} [CommSemiring R]
    (slots : List (SymbolicCost.RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ SymbolicCost.Retained D a)
    (P : SymbolicCost.CoeffList D R) :
    SymbolicCost.denote (SymbolicCost.project slots P) =
      Truncation.canonical (D + 1) D (2 * D + 1) (SymbolicCost.denote P) := by
  simpa [SymbolicCost.denseAdd, SymbolicCost.denote] using
    SymbolicCost.denseAdd_denote slots hn hs P []

/-- Executing the real dense-list operations computes the canonical truncation
of the full polynomial expression. No full polynomial is built by the execution. -/
theorem eval_dense_denote {D : ℕ} {R : Type*} [CommSemiring R]
    (slots : List (SymbolicCost.RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ SymbolicCost.Retained D a)
    (e : Expr (SymbolicCost.CoeffList D R)) :
    SymbolicCost.denote ((e.map (Dense.ofRaw slots)).eval).coefficients =
      Truncation.canonical (D + 1) D (2 * D + 1)
        ((e.map SymbolicCost.denote).eval) := by
  induction e with
  | lit P => exact denote_project slots hn hs P
  | add e f he hf =>
      change SymbolicCost.denote (SymbolicCost.denseAdd slots _ _) = _
      rw [SymbolicCost.denseAdd_denote slots hn hs, he, hf]
      simpa only [Expr.map, Expr.eval, Truncation.canonical_add] using
        congrArg₂ (fun x y => x + y)
          (canonical_idempotent (D + 1) D (2 * D + 1) ((e.map SymbolicCost.denote).eval))
          (canonical_idempotent (D + 1) D (2 * D + 1) ((f.map SymbolicCost.denote).eval))
  | mul e f he hf =>
      change SymbolicCost.denote (SymbolicCost.denseMul slots _ _) = _
      rw [SymbolicCost.denseMul_denote slots hn hs, he, hf]
      exact Truncation.canonical_mul _ _ _ _ _

theorem eval_retainedDense_denote {D : ℕ} {R : Type*} [CommSemiring R]
    (e : Expr (SymbolicCost.CoeffList D R)) :
    SymbolicCost.denote ((e.map (Dense.ofRaw (retainedSlots D))).eval).coefficients =
      Truncation.canonical (D + 1) D (2 * D + 1)
        ((e.map SymbolicCost.denote).eval) :=
  eval_dense_denote (retainedSlots D) (retainedSlots_nodup D) (mem_retainedSlots D) e

/-! ## Finite coefficient extraction after moment execution -/

/-- Sum explicitly requested coefficients. Each requested index is scanned by
the executable backend, and the counter also charges the final scalar addition. -/
def collectCoefficientsWithCost {D : ℕ} {R : Type*} [Semiring R]
    (P : SymbolicCost.CoeffList D R) : List (SymbolicCost.RawIndex D) → R × ℕ
  | [] => (0, 0)
  | a :: indices =>
      let first := SymbolicCost.scanWithCost P a
      let rest := collectCoefficientsWithCost P indices
      (first.1 + rest.1, first.2 + rest.2 + 1)

theorem collectCoefficientsWithCost_eq {D : ℕ} {R : Type*} [Semiring R]
    (P : SymbolicCost.CoeffList D R) (indices : List (SymbolicCost.RawIndex D)) :
    collectCoefficientsWithCost P indices =
      ((indices.map (SymbolicCost.coeff P)).sum, indices.length * (3 * P.length + 1)) := by
  induction indices with
  | nil => simp [collectCoefficientsWithCost]
  | cons a indices ih =>
      simp only [collectCoefficientsWithCost, SymbolicCost.scanWithCost_eq, ih,
        List.map_cons, List.sum_cons, List.length_cons ]
      congr 1
      ring

/-- Summing the retained U coefficients is performed after selecting X^a. -/
def collapseU {D : ℕ} {R : Type*} [Semiring R]
    (a : Fin D → ℕ) (r : ℕ) (P : SymbolicCost.CoeffList D R) : R :=
  (collectCoefficientsWithCost P
    ((List.range (D + 1)).map fun j => (a, (j, r)))).1

theorem collapseU_eq {D : ℕ} {R : Type*} [Semiring R]
    (a : Fin D → ℕ) (r : ℕ) (P : SymbolicCost.CoeffList D R) :
    collapseU a r P =
      ((List.range (D + 1)).map fun j => SymbolicCost.coeff P (a, (j, r))).sum := by
  simp [collapseU, collectCoefficientsWithCost_eq, List.map_map, Function.comp_def]

abbrev MomentResult (D : ℕ) (R : Type*) :=
  (Fin D → ℕ) × SymbolicCost.CoeffList D R

/-- One output Z coefficient, accumulated over all supplied moment results. -/
def finishAtWithCost {D : ℕ} {R : Type*} [Semiring R]
    (r : ℕ) : List (MomentResult D R) → R × ℕ
  | [] => (0, 0)
  | m :: ms =>
      let current := collectCoefficientsWithCost m.2
        ((List.range (D + 1)).map fun j => (m.1, (j, r)))
      let rest := finishAtWithCost r ms
      (current.1 + rest.1, current.2 + rest.2 + 1)

theorem finishAtWithCost_eq {D : ℕ} {R : Type*} [Semiring R]
    (r : ℕ) (ms : List (MomentResult D R)) :
    finishAtWithCost r ms =
      ((ms.map fun m => collapseU m.1 r m.2).sum,
        (ms.map fun m => (D + 1) * (3 * m.2.length + 1) + 1).sum) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      simp only [finishAtWithCost, collectCoefficientsWithCost_eq, ih,
        List.length_map, List.length_range, List.map_cons, List.sum_cons ]
      simp only [collapseU_eq, List.map_map, Function.comp_def]
      congr 1
      omega

/-- The final jet is a list of its first D coefficients. All loops are finite;
the accompanying count includes coefficient scans and scalar accumulation. -/
def finishMomentsWithCost {D : ℕ} {R : Type*} [Semiring R]
    (ms : List (MomentResult D R)) : List R × ℕ :=
  let rows := (List.range D).map fun r => finishAtWithCost r ms
  (rows.map Prod.fst, (rows.map Prod.snd).sum + D)

theorem finishMomentsWithCost_eq {D : ℕ} {R : Type*} [Semiring R]
    (ms : List (MomentResult D R)) :
    finishMomentsWithCost ms =
      ((List.range D).map (fun r => (ms.map fun m => collapseU m.1 r m.2).sum),
        D * (ms.map fun m => (D + 1) * (3 * m.2.length + 1) + 1).sum + D) := by
  simp [finishMomentsWithCost, finishAtWithCost_eq, List.map_map, Function.comp_def]

/-- Execute each selected moment exactly once, then extract its coefficient
contributions. The list of moment indices is the constructive weak-composition
enumeration proved above. -/
def executeMoments {D : ℕ} {R : Type*} [Semiring R]
    (program : (Fin D → ℕ) → Expr (Dense (retainedSlots D) R)) : List (MomentResult D R) :=
  (exponentList D (2 * D + 1)).map fun a => (a, (program a).execute.coefficients)

def executeJet {D : ℕ} {R : Type*} [Semiring R]
    (program : (Fin D → ℕ) → Expr (Dense (retainedSlots D) R)) : List R :=
  (finishMomentsWithCost (executeMoments program)).1

theorem executeJet_eq {D : ℕ} {R : Type*} [Semiring R]
    (program : (Fin D → ℕ) → Expr (Dense (retainedSlots D) R)) :
    executeJet program = (List.range D).map fun r =>
      ((exponentList D (2 * D + 1)).map fun a =>
        collapseU a r (program a).eval.coefficients).sum := by
  simp [executeJet, executeMoments, finishMomentsWithCost_eq, List.map_map,
    Function.comp_def]

theorem executeJet_length {D : ℕ} {R : Type*} [Semiring R]
    (program : (Fin D → ℕ) → Expr (Dense (retainedSlots D) R)) :
    (executeJet program).length = D := by
  simp [executeJet_eq]

/-- The finishing counter is polynomial in D times the moment count times the
retained coefficient-list length. It does not enumerate input assignments. -/
theorem executeJet_finishing_cost {D : ℕ} {R : Type*} [Semiring R]
    (program : (Fin D → ℕ) → Expr (Dense (retainedSlots D) R)) :
    (finishMomentsWithCost (executeMoments program)).2 =
      D * ((3 * D + 1).choose D *
        ((D + 1) * (3 * (retainedSlots D).length + 1) + 1)) + D := by
  rw [finishMomentsWithCost_eq]
  simp only [ executeMoments, List.map_map, Function.comp_def, Dense.length_eq]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [exponentList_length]
  have he : D + (2 * D + 1) = 3 * D + 1 := by omega
  rw [he]

/-- Semantic version of coefficient extraction, used only to state correctness. -/
noncomputable def extractPolynomial {ι R : Type*} [CommSemiring R]
    (a : ι →₀ ℕ) (P : Truncation.Poly ι R) : Polynomial R :=
  (Truncation.mapCoeffs (Truncation.mapCoeffs (MvPolynomial.coeffAddMonoidHom a)) P).eval 1

theorem extract_canonical_coeff {ι R : Type*} [CommSemiring R]
    (μ D N : ℕ) (a : ι →₀ ℕ) (ha : a.sum (fun _ n => n) ≤ N)
    (P : Truncation.Poly ι R) (r : ℕ) (hr : r < D) :
    (extractPolynomial a (Truncation.canonical μ D N P)).coeff r =
      ∑ j ∈ Finset.range μ, ((P.coeff j).coeff r).coeff a := by
  simp [extractPolynomial, Truncation.canonical, Truncation.mapCoeffs_monomial,
    Truncation.coeff_xTrunc, Polynomial.eval_finsetSum,
    Polynomial.coeff_monomial, ha, hr]

/-- The executable scan is precisely extraction of X^a followed by U=1 on a
canonical representative. The order of these operations is explicit. -/
theorem collapseU_eq_extract_of_canonical {D : ℕ} {R : Type*} [CommSemiring R]
    (a : Fin D → ℕ) (ha : ∑ i, a i ≤ 2 * D + 1)
    (r : ℕ) (hr : r < D) (P : SymbolicCost.CoeffList D R)
    (hP : Truncation.canonical (D + 1) D (2 * D + 1) (SymbolicCost.denote P) =
      SymbolicCost.denote P) :
    collapseU a r P =
      (extractPolynomial (Finsupp.equivFunOnFinite.symm a) (SymbolicCost.denote P)).coeff r := by
  have ha' : (Finsupp.equivFunOnFinite.symm a : Fin D →₀ ℕ).sum (fun _ n => n) ≤
      2 * D + 1 := by simpa [Finsupp.sum_fintype] using ha
  have hrange : (List.range (D + 1)).toFinset = Finset.range (D + 1) := by
    ext j
    simp
  calc
    collapseU a r P = ∑ j ∈ Finset.range (D + 1),
        SymbolicCost.polyCoeff (SymbolicCost.denote P) (a, (j, r)) := by
      rw [collapseU_eq]
      simp only [SymbolicCost.polyCoeff_denote]
      simpa [hrange] using (List.sum_toFinset
        (fun j => SymbolicCost.coeff P (a, (j, r)))
        (l := List.range (D + 1)) List.nodup_range).symm
    _ = (extractPolynomial (Finsupp.equivFunOnFinite.symm a)
        (Truncation.canonical (D + 1) D (2 * D + 1) (SymbolicCost.denote P))).coeff r := by
      symm
      exact extract_canonical_coeff (D + 1) D (2 * D + 1) _ ha' _ r hr
    _ = _ := by rw [hP]

/-- Fully executable polynomial-expression-to-jet code. Its input is finite
coefficient syntax for each requested moment, not a count or satisfiability oracle. -/
def executeRawJet {D : ℕ} {R : Type*} [Semiring R]
    (program : (Fin D → ℕ) → Expr (SymbolicCost.CoeffList D R)) : List R :=
  executeJet (fun a => (program a).map (Dense.ofRaw (retainedSlots D)))

/-- The concrete jet code implements the canonical symbolic moment formula.
Identifying the supplied moment programs with the layout's grouped factors is
the subsequent mathematical integration step, not part of this hypothesis. -/
theorem executeRawJet_eq {D : ℕ} {R : Type*} [CommSemiring R]
    (program : (Fin D → ℕ) → Expr (SymbolicCost.CoeffList D R)) :
    executeRawJet program = (List.range D).map fun r =>
      ((exponentList D (2 * D + 1)).map fun a =>
        (extractPolynomial (Finsupp.equivFunOnFinite.symm a)
          (Truncation.canonical (D + 1) D (2 * D + 1)
            (((program a).map SymbolicCost.denote).eval))).coeff r).sum := by
  rw [executeRawJet, executeJet_eq]
  apply List.map_congr_left
  intro r hr
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have hden := eval_retainedDense_denote (program a)
  have hcan : Truncation.canonical (D + 1) D (2 * D + 1)
      (SymbolicCost.denote (((program a).map
        (Dense.ofRaw (retainedSlots D))).eval.coefficients)) =
      SymbolicCost.denote (((program a).map
        (Dense.ofRaw (retainedSlots D))).eval.coefficients) := by
    rw [hden, canonical_idempotent]
  rw [collapseU_eq_extract_of_canonical a
    ((mem_exponentList D (2 * D + 1) a).mp ha) r (List.mem_range.mp hr) _ hcan]
  rw [hden]

/-- One weighted group evaluation. The group itself is executable syntax,
so its computation cost is included rather than assumed to be one operation. -/
structure WeightedTerm (R : Type u) where
  weight : R
  group : Expr R

namespace WeightedTerm

variable {R : Type u}

def expression (t : WeightedTerm R) : Expr R := .mul (.lit t.weight) t.group

@[simp] theorem expression_eval [Add R] [Mul R] (t : WeightedTerm R) :
    t.expression.eval = t.weight * t.group.eval := rfl

@[simp] theorem expression_size (t : WeightedTerm R) :
    t.expression.size = t.group.size + 2 := by
  simp [expression, Expr.size]; omega

end WeightedTerm

/-- The two separate inner lists for one fixed choice of outer data. -/
structure Block (R : Type u) where
  outside : R
  left : List (WeightedTerm R)
  right : List (WeightedTerm R)

namespace Block

variable {R : Type u}

/-- Assemble one separated block from explicit inner enumeration lists. The
functions supply finite syntax for group computations, not their truth values. -/
def ofFunctions {X Y : Type*} (c : R) (xs : List X) (ys : List Y)
    (w₀ : X → R) (w₁ : Y → R) (B₀ : Y → Expr R) (B₁ : X → Expr R) : Block R :=
  ⟨c, xs.map (fun x => ⟨w₀ x, B₁ x⟩), ys.map (fun y => ⟨w₁ y, B₀ y⟩)⟩

/-- The implementation of the product of the two independent sums in (4.8). -/
def expression [Zero R] (b : Block R) : Expr R :=
  .mul (.mul (.lit b.outside) (Expr.sum (b.left.map WeightedTerm.expression)))
    (Expr.sum (b.right.map WeightedTerm.expression))

def innerCalls (b : Block R) : ℕ := b.left.length + b.right.length

def groupInstructions (b : Block R) : ℕ :=
  (b.left.map fun t => t.group.size).sum + (b.right.map fun t => t.group.size).sum

@[simp] theorem expression_eval [Semiring R] (b : Block R) :
    b.expression.eval =
      b.outside * (b.left.map fun t => t.weight * t.group.eval).sum *
        (b.right.map fun t => t.weight * t.group.eval).sum := by
  simp [expression, Expr.eval, List.map_map, Function.comp_def]

private theorem term_sizes (ts : List (WeightedTerm R)) :
    (ts.map fun t => t.expression.size).sum =
      (ts.map fun t => t.group.size).sum + 2 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih, WeightedTerm.expression_size]
      omega

/-- Exact instruction count, with no product of the two inner-list lengths. -/
theorem expression_size [Zero R] (b : Block R) :
    b.expression.size = b.groupInstructions + 3 * b.innerCalls + 5 := by
  simp only [expression, Expr.size, Expr.size_sum, List.map_map,
    Function.comp_def, List.length_map, term_sizes, groupInstructions, innerCalls]
  omega

/-- The finite-list program agrees with the finite-set separated sum. Nodup
certifies that each coset element is enumerated exactly once. -/
theorem ofFunctions_eval_finset [CommSemiring R]
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (c : R) (xs : List X) (ys : List Y) (hx : xs.Nodup) (hy : ys.Nodup)
    (w₀ : X → R) (w₁ : Y → R) (B₀ : Y → Expr R) (B₁ : X → Expr R) :
    (ofFunctions c xs ys w₀ w₁ B₀ B₁).expression.eval =
      ∑ x ∈ xs.toFinset, ∑ y ∈ ys.toFinset,
        c * w₀ x * w₁ y * (B₀ y).eval * (B₁ x).eval := by
  rw [Separation.separated_sum]
  simp only [expression_eval, ofFunctions, List.map_map, Function.comp_def]
  rw [List.sum_toFinset _ hx, List.sum_toFinset _ hy]

end Block

/-- The list implementation agrees with (4.8) for input-dependent group
programs whose denotations satisfy the actual independence hypotheses. -/
theorem block_eval_of_independent {R X Y : Type*} [CommSemiring R]
    [DecidableEq X] [DecidableEq Y]
    (xs : List X) (ys : List Y) (hx : xs.Nodup) (hy : ys.Nodup)
    (r₀ : X) (r₁ : Y) (hr₀ : r₀ ∈ xs) (hr₁ : r₁ ∈ ys)
    (A₀ A₁ : X → Y → Expr R) (w : X → Y → R)
    (c : R) (w₀ : X → R) (w₁ : Y → R)
    (h₀ : ∀ x ∈ xs, ∀ x' ∈ xs, ∀ y ∈ ys, (A₀ x y).eval = (A₀ x' y).eval)
    (h₁ : ∀ x ∈ xs, ∀ y ∈ ys, ∀ y' ∈ ys, (A₁ x y).eval = (A₁ x y').eval)
    (hw : ∀ x ∈ xs, ∀ y ∈ ys, w x y = c * w₀ x * w₁ y) :
    (Block.ofFunctions c xs ys w₀ w₁ (A₀ r₀) (fun x => A₁ x r₁)).expression.eval =
      ∑ x ∈ xs.toFinset, ∑ y ∈ ys.toFinset,
        w x y * (A₀ x y).eval * (A₁ x y).eval := by
  rw [Separation.weighted_separation xs.toFinset ys.toFinset r₀ r₁
    (List.mem_toFinset.mpr hr₀) (List.mem_toFinset.mpr hr₁)
    (fun x y => (A₀ x y).eval) (fun x y => (A₁ x y).eval) w c w₀ w₁
    (by simpa only [List.mem_toFinset] using h₀)
    (by simpa only [List.mem_toFinset] using h₁)
    (by simpa only [List.mem_toFinset] using hw)]
  simp only [Block.expression_eval, Block.ofFunctions, List.map_map, Function.comp_def]
  rw [List.sum_toFinset _ hx, List.sum_toFinset _ hy]

/-- One moment is the sum over all supplied outer-data blocks. -/
def momentExpression {R : Type u} [Zero R] (blocks : List (Block R)) : Expr R :=
  Expr.sum (blocks.map Block.expression)

theorem momentExpression_eval {R : Type u} [Semiring R] (blocks : List (Block R)) :
    (momentExpression blocks).eval =
      (blocks.map fun b =>
        b.outside * (b.left.map fun t => t.weight * t.group.eval).sum *
          (b.right.map fun t => t.weight * t.group.eval).sum).sum := by
  simp [momentExpression, List.map_map, Function.comp_def]

/-- Exact size of all arithmetic instructions in one separated moment. -/
theorem momentExpression_size {R : Type u} [Zero R] (blocks : List (Block R)) :
    (momentExpression blocks).size =
      (blocks.map Block.groupInstructions).sum +
        3 * (blocks.map Block.innerCalls).sum + 6 * blocks.length + 1 := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
      change b.expression.size + (momentExpression bs).size + 1 = _
      rw [b.expression_size, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- The concrete compiled separated loop has an execution certificate at its
proved instruction bound. Coefficient arithmetic and loads are still macrosteps. -/
theorem momentExpression_trace {R : Type u} [Zero R] [Add R] [Mul R]
    (blocks : List (Block R)) :
    Computation.Trace step
      ((blocks.map Block.groupInstructions).sum +
        3 * (blocks.map Block.innerCalls).sum + 6 * blocks.length + 1)
      ⟨(momentExpression blocks).compile, []⟩
      ⟨[], [(momentExpression blocks).eval]⟩ := by
  rw [← momentExpression_size]
  simpa using (momentExpression blocks).compile_trace [] []

namespace Expr

theorem map_sum {R S : Type*} [Zero R] [Zero S]
    (f : R → S) (hf : f 0 = 0) (es : List (Expr R)) :
    (Expr.sum es).map f = Expr.sum (es.map fun e => e.map f) := by
  induction es with
  | nil => simp [Expr.sum, Expr.map, hf]
  | cons e es ih => simp [Expr.sum, Expr.map, ih]

end Expr

namespace WeightedTerm

def map {R S : Type*} (f : R → S) (t : WeightedTerm R) : WeightedTerm S :=
  ⟨f t.weight, t.group.map f⟩

theorem map_expression {R S : Type*} (f : R → S) (t : WeightedTerm R) :
    t.expression.map f = (t.map f).expression := rfl

end WeightedTerm

namespace Block

def map {R S : Type*} (f : R → S) (b : Block R) : Block S :=
  ⟨f b.outside, b.left.map (WeightedTerm.map f), b.right.map (WeightedTerm.map f)⟩

theorem map_expression {R S : Type*} [Zero R] [Zero S]
    (f : R → S) (hf : f 0 = 0) (b : Block R) :
    b.expression.map f = (b.map f).expression := by
  simp [expression, Expr.map, Expr.map_sum f hf, map,
    List.map_map, WeightedTerm.map_expression, Function.comp_def]

end Block

theorem map_momentExpression {R S : Type*} [Zero R] [Zero S]
    (f : R → S) (hf : f 0 = 0) (blocks : List (Block R)) :
    (momentExpression blocks).map f =
      momentExpression (blocks.map (Block.map f)) := by
  simp [momentExpression, Expr.map_sum f hf, List.map_map,
    Block.map_expression f hf, Function.comp_def]

/-- The source-code builder for a separated moment. A raw coefficient-list
zero is the empty list; no operations on full polynomials are executed. -/
def rawMomentExpression {D : ℕ} {R : Type*}
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    Expr (SymbolicCost.CoeffList D R) :=
  letI : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  momentExpression blocks

theorem rawMomentExpression_size {D : ℕ} {R : Type*}
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    (rawMomentExpression blocks).size =
      (blocks.map Block.groupInstructions).sum +
        3 * (blocks.map Block.innerCalls).sum + 6 * blocks.length + 1 := by
  let _ : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  exact momentExpression_size blocks

/-- Denotation of the explicit input programs for one separated moment. -/
noncomputable def rawMomentValue {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) : SymbolicCost.Poly D R :=
  (blocks.map fun b => SymbolicCost.denote b.outside *
    (b.left.map fun t => SymbolicCost.denote t.weight *
      (t.group.map SymbolicCost.denote).eval).sum *
    (b.right.map fun t => SymbolicCost.denote t.weight *
      (t.group.map SymbolicCost.denote).eval).sum).sum

theorem rawMomentExpression_value {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    ((rawMomentExpression blocks).map SymbolicCost.denote).eval = rawMomentValue blocks := by
  let _ : Zero (SymbolicCost.CoeffList D R) := ⟨[]⟩
  change ((momentExpression blocks).map SymbolicCost.denote).eval = _
  rw [map_momentExpression SymbolicCost.denote (by rfl), momentExpression_eval]
  simp [rawMomentValue, Block.map, WeightedTerm.map, List.map_map, Function.comp_def]

/-- The separated finite counting kernel: build two inner sums per outer datum,
execute each moment over actual dense coefficient lists, and extract the jet. -/
def executeSeparatedJet {D : ℕ} {R : Type*} [Semiring R]
    (blocks : (Fin D → ℕ) → List (Block (SymbolicCost.CoeffList D R))) : List R :=
  executeRawJet (fun a => rawMomentExpression (blocks a))

/-- Correctness of the actual separated kernel relative to its explicit input
group programs. The RHS is the canonical-moment expression of (4.7)-(4.8). -/
theorem executeSeparatedJet_eq {D : ℕ} {R : Type*} [CommSemiring R]
    (blocks : (Fin D → ℕ) → List (Block (SymbolicCost.CoeffList D R))) :
    executeSeparatedJet blocks = (List.range D).map fun r =>
      ((exponentList D (2 * D + 1)).map fun a =>
        (extractPolynomial (Finsupp.equivFunOnFinite.symm a)
          (Truncation.canonical (D + 1) D (2 * D + 1)
            (rawMomentValue (blocks a)))).coeff r).sum := by
  rw [executeSeparatedJet, executeRawJet_eq]
  simp only [rawMomentExpression_value]

/-- The dense execution cost of a separated moment includes every group
instruction and only the sum of the two inner-list lengths. -/
theorem rawMomentExpression_dense_cost {D : ℕ} {R : Type*} [Semiring R]
    (blocks : List (Block (SymbolicCost.CoeffList D R))) :
    ((rawMomentExpression blocks).map (Dense.ofRaw (retainedSlots D))).cost
        (Dense.costs (retainedSlots D)) ≤
      Dense.instructionBudget (retainedSlots D) *
        ((blocks.map Block.groupInstructions).sum +
          3 * (blocks.map Block.innerCalls).sum + 6 * blocks.length + 1) := by
  simpa only [Expr.size_map, rawMomentExpression_size] using
    denseExpression_cost_le (retainedSlots D)
      ((rawMomentExpression blocks).map (Dense.ofRaw (retainedSlots D)))

end SubexponentialSAT.Algorithm

end OAI.Algorithms
