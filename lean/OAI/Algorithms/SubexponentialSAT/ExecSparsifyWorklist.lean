import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BranchTree
import OAI.Algorithms.SubexponentialSAT.Sparsify
import OAI.Algorithms.SubexponentialSAT.QuantitativeBranchTree
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerSearch
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost

namespace OAI.Algorithms

/-!
# Executable depth-first worklist traversal for sparsification

The traversal manipulates a list of pending inputs explicitly. It never builds
the specification tree while running. A decreasing mass supplies a finite fuel
bound; the fuel loop halts as soon as the worklist is empty. The specification
tree is used only to prove the exact number of visited nodes.
-/

namespace SubexponentialSAT.ExecSparsifyWorklist

variable {α : Type*}

/-- A computable binary branching operation with a strict mass decrease in
each child. The decrease proof is erased by execution. -/
structure Branching (α : Type*) where
  split : α → Option (α × α)
  mass : α → ℕ
  decreases : ∀ x a b, split x = some (a, b) → mass a < mass x ∧ mass b < mass x

/-- The explicit traversal state. `leaves` is accumulated in reverse order. -/
structure State (α : Type*) where
  pending : List α
  leaves : List α
  visits : ℕ
  deriving Repr

def initial (x : α) : State α := ⟨[x], [], 0⟩

/-- A single worklist transition. Pushing A before B makes this depth-first. -/
def step (split : α → Option (α × α)) (s : State α) : State α :=
  match s.pending with
  | [] => s
  | x :: rest =>
      match split x with
      | none => ⟨rest, x :: s.leaves, s.visits + 1⟩
      | some (a, b) => ⟨a :: b :: rest, s.leaves, s.visits + 1⟩

/-- Partial transition semantics: the empty worklist is terminal. This is a
coarse list transition, not a primitive machine step. -/
def transition (split : α → Option (α × α)) (s : State α) : Option (State α) :=
  match s.pending with
  | [] => none
  | _ :: _ => some (step split s)

theorem step_visits (split : α → Option (α × α)) (s : State α)
    (h : s.pending ≠ []) : (step split s).visits = s.visits + 1 := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => exact False.elim (h rfl)
  | cons x xs => cases hs : split x <;> simp [step, hs]

/-- Primitive recursion on a numeric fuel bound, stopping immediately when
the pending list becomes empty. -/
def runFuel (split : α → Option (α × α)) : ℕ → State α → State α
  | 0, s => s
  | fuel + 1, s =>
      match s.pending with
      | [] => s
      | _ :: _ => runFuel split fuel (step split s)

/-- The recursive program produces a genuine finite transition trace. Its
length is exactly the increase in the visit counter. -/
theorem runFuel_execution (split : α → Option (α × α)) (fuel : ℕ) (s : State α) :
    ∃ q, Computation.Trace (transition split) q s (runFuel split fuel s) ∧
      (runFuel split fuel s).visits = s.visits + q := by
  induction fuel generalizing s with
  | zero => exact ⟨0, .refl _, by simp [runFuel]⟩
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => exact ⟨0, by simpa [runFuel, hp] using Computation.Trace.refl s,
        by simp [runFuel, hp]⟩
    | cons x xs =>
      obtain ⟨q, hq, hv⟩ := ih (step split s)
      have hn : s.pending ≠ [] := by rw [hp]; simp
      refine ⟨q + 1, ?_, ?_⟩
      · simpa only [runFuel, hp] using
          Computation.Trace.cons (show transition split s = some (step split s) by
            simp [transition, hp]) hq
      · simp only [runFuel, hp]
        rw [hv, step_visits split s hn]
        omega

def potential (mass : α → ℕ) (pending : List α) : ℕ :=
  (pending.map fun x => 3 ^ mass x).sum

@[simp] theorem potential_nil (mass : α → ℕ) : potential mass [] = 0 := rfl

@[simp] theorem potential_cons (mass : α → ℕ) (x : α) (xs : List α) :
    potential mass (x :: xs) = 3 ^ mass x + potential mass xs := rfl

theorem pow_mass_children_lt {ma mb m : ℕ} (ha : ma < m) (hb : mb < m) :
    3 ^ ma + 3 ^ mb < 3 ^ m := by
  cases m with
  | zero => omega
  | succ m =>
    have ha' : 3 ^ ma ≤ 3 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    have hb' : 3 ^ mb ≤ 3 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    have hp : 0 < 3 ^ m := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

theorem potential_eq_zero_iff (mass : α → ℕ) (pending : List α) :
    potential mass pending = 0 ↔ pending = [] := by
  cases pending with
  | nil => simp
  | cons x xs =>
    have hp : 0 < 3 ^ mass x := Nat.pow_pos (by decide)
    simp only [potential_cons, List.cons_ne_nil, iff_false]
    omega

theorem step_potential_lt (branch : Branching α) (s : State α)
    (h : s.pending ≠ []) :
    potential branch.mass (step branch.split s).pending < potential branch.mass s.pending := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => exact False.elim (h rfl)
  | cons x xs =>
    cases hs : branch.split x with
    | none =>
      have hp : 0 < 3 ^ branch.mass x := Nat.pow_pos (by decide)
      simp only [step, hs, potential_cons]
      omega
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hd := branch.decreases x a b hs
      have hp := pow_mass_children_lt hd.1 hd.2
      simp only [step, hs, potential_cons]
      omega

/-- The fuel bound is derived from the mass decrease, independently of any
claimed sparsification node bound. -/
theorem runFuel_pending_nil (branch : Branching α) (fuel : ℕ) (s : State α)
    (h : potential branch.mass s.pending ≤ fuel) :
    (runFuel branch.split fuel s).pending = [] := by
  induction fuel generalizing s with
  | zero =>
    have hz : potential branch.mass s.pending = 0 := by omega
    exact (potential_eq_zero_iff branch.mass s.pending).mp hz
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simp [runFuel, hp]
    | cons x xs =>
      have hn : s.pending ≠ [] := by rw [hp]; simp
      have hd := step_potential_lt branch s hn
      have hnext : potential branch.mass (step branch.split s).pending ≤ fuel := by omega
      simpa only [runFuel, hp] using ih (step branch.split s) hnext

/-- The actual worklist program. The large fuel is represented as an integer;
unused fuel is never iterated after the worklist becomes empty. -/
def run (branch : Branching α) (s : State α) : State α :=
  runFuel branch.split (potential branch.mass s.pending) s

theorem run_pending_nil (branch : Branching α) (s : State α) :
    (run branch s).pending = [] :=
  runFuel_pending_nil branch _ s le_rfl

def ListOr (P : α → Prop) (xs : List α) : Prop := ∃ x ∈ xs, P x

@[simp] theorem ListOr_nil (P : α → Prop) : ¬ ListOr P [] := by simp [ListOr]

@[simp] theorem ListOr_cons (P : α → Prop) (x : α) (xs : List α) :
    ListOr P (x :: xs) ↔ P x ∨ ListOr P xs := by simp [ListOr]

def Covers (P : α → Prop) (s : State α) : Prop :=
  ListOr P s.pending ∨ ListOr P s.leaves

def SplitSound (split : α → Option (α × α)) (P : α → Prop) : Prop :=
  ∀ x a b, split x = some (a, b) → (P x ↔ P a ∨ P b)

theorem step_covers (split : α → Option (α × α)) (P : α → Prop)
    (hsound : SplitSound split P) (s : State α) :
    Covers P (step split s) ↔ Covers P s := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => rfl
  | cons x xs =>
    cases hs : split x with
    | none =>
      simp only [step, hs, Covers, ListOr_cons]
      tauto
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hiff := hsound x a b hs
      simp only [step, hs, Covers, ListOr_cons]
      tauto

theorem runFuel_covers (split : α → Option (α × α)) (P : α → Prop)
    (hsound : SplitSound split P) (fuel : ℕ) (s : State α) :
    Covers P (runFuel split fuel s) ↔ Covers P s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simp only [runFuel, hp]
    | cons x xs =>
      simp only [runFuel, hp]
      exact (ih (step split s)).trans (step_covers split P hsound s)

theorem run_leaves_cover (branch : Branching α) (P : α → Prop)
    (hsound : SplitSound branch.split P) (s : State α) :
    ListOr P (run branch s).leaves ↔ Covers P s := by
  have h := runFuel_covers branch.split P hsound (potential branch.mass s.pending) s
  change Covers P (run branch s) ↔ Covers P s at h
  simpa only [Covers, run_pending_nil, ListOr_nil, false_or] using h

theorem initial_run_correct (branch : Branching α) (P : α → Prop)
    (hsound : SplitSound branch.split P) (x : α) :
    P x ↔ ∃ y ∈ (run branch (initial x)).leaves, P y := by
  have h := run_leaves_cover branch P hsound (initial x)
  simpa [initial, Covers, ListOr] using h.symm

def Terminal (split : α → Option (α × α)) (x : α) : Prop := split x = none

theorem step_leaves_terminal (split : α → Option (α × α)) (s : State α)
    (h : ∀ x ∈ s.leaves, Terminal split x) :
    ∀ x ∈ (step split s).leaves, Terminal split x := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => exact h
  | cons x xs =>
    cases hs : split x with
    | none =>
      intro y hy
      simp only [step, hs] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hs
      · exact h y hy
    | some pair => simpa only [step, hs] using h

theorem runFuel_leaves_terminal (split : α → Option (α × α))
    (fuel : ℕ) (s : State α) (h : ∀ x ∈ s.leaves, Terminal split x) :
    ∀ x ∈ (runFuel split fuel s).leaves, Terminal split x := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simpa only [runFuel, hp] using h
    | cons x xs =>
      simpa only [runFuel, hp] using
        ih (step split s) (step_leaves_terminal split s h)

theorem initial_run_leaves_terminal (branch : Branching α) (x : α) :
    ∀ y ∈ (run branch (initial x)).leaves, Terminal branch.split y :=
  runFuel_leaves_terminal branch.split _ _ (by simp [initial])

def Invariant (P : α → Prop) (s : State α) : Prop :=
  (∀ x ∈ s.pending, P x) ∧ ∀ x ∈ s.leaves, P x

def SplitClosed (split : α → Option (α × α)) (P : α → Prop) : Prop :=
  ∀ x a b, P x → split x = some (a, b) → P a ∧ P b

theorem step_invariant (split : α → Option (α × α)) (P : α → Prop)
    (hclosed : SplitClosed split P) (s : State α) (h : Invariant P s) :
    Invariant P (step split s) := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => exact h
  | cons x xs =>
    have hx : P x := h.1 x List.mem_cons_self
    have hxs : ∀ y ∈ xs, P y := fun y hy => h.1 y (List.mem_cons_of_mem _ hy)
    cases hs : split x with
    | none =>
      simp only [Invariant, step, hs]
      refine ⟨hxs, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact h.2 y hy
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hab := hclosed x a b hx hs
      simp only [Invariant, step, hs]
      refine ⟨?_, h.2⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hab.1
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hab.2
      · exact hxs y hy

theorem runFuel_invariant (split : α → Option (α × α)) (P : α → Prop)
    (hclosed : SplitClosed split P) (fuel : ℕ) (s : State α) (h : Invariant P s) :
    Invariant P (runFuel split fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simpa only [runFuel, hp] using h
    | cons x xs =>
      simpa only [runFuel, hp] using ih (step split s) (step_invariant split P hclosed s h)

theorem initial_run_leaves_invariant (branch : Branching α) (P : α → Prop)
    (hclosed : SplitClosed branch.split P) (x : α) (hx : P x) :
    ∀ y ∈ (run branch (initial x)).leaves, P y := by
  have hinit : Invariant P (initial x) := by simpa [Invariant, initial] using hx
  exact (runFuel_invariant branch.split P hclosed _ _ hinit).2

/-- A specification tree for one input, built by well-founded recursion on
the literal-mass measure. It is not materialized by `run`. -/
def tree (branch : Branching α) (x : α) : BranchTree.Tree :=
  match _h : branch.split x with
  | none => .leaf
  | some (a, b) => .branch (tree branch a) (tree branch b)
termination_by branch.mass x
decreasing_by
  · exact (branch.decreases x a b _h).1
  · exact (branch.decreases x a b _h).2

theorem tree_none (branch : Branching α) (x : α) (h : branch.split x = none) :
    tree branch x = .leaf := by rw [tree, h]

theorem tree_some (branch : Branching α) (x a b : α)
    (h : branch.split x = some (a, b)) :
    tree branch x = .branch (tree branch a) (tree branch b) := by rw [tree, h]

def forestNodes (branch : Branching α) (xs : List α) : ℕ :=
  (xs.map fun x => (tree branch x).nodeCount).sum

@[simp] theorem forestNodes_nil (branch : Branching α) : forestNodes branch [] = 0 := rfl

@[simp] theorem forestNodes_cons (branch : Branching α) (x : α) (xs : List α) :
    forestNodes branch (x :: xs) = (tree branch x).nodeCount + forestNodes branch xs := rfl

/-- One explicit worklist transition visits exactly one node of the remaining
specification forest. -/
theorem step_node_conservation (branch : Branching α) (s : State α) :
    (step branch.split s).visits + forestNodes branch (step branch.split s).pending =
      s.visits + forestNodes branch s.pending := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => rfl
  | cons x xs =>
    cases hs : branch.split x with
    | none =>
      simp only [step, hs, forestNodes_cons, tree_none branch x hs, BranchTree.Tree.nodeCount]
      omega
    | some pair =>
      rcases pair with ⟨a, b⟩
      simp only [step, hs, forestNodes_cons, tree_some branch x a b hs,
        BranchTree.Tree.nodeCount]
      omega

theorem runFuel_node_conservation (branch : Branching α) (fuel : ℕ) (s : State α) :
    (runFuel branch.split fuel s).visits +
        forestNodes branch (runFuel branch.split fuel s).pending =
      s.visits + forestNodes branch s.pending := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simp only [runFuel, hp]
    | cons x xs =>
      simpa only [runFuel, hp] using
        (ih (step branch.split s)).trans (step_node_conservation branch s)

/-- The program's visit counter equals the exact number of processed tree
nodes; it is not an assumed running-time annotation. -/
theorem run_visits (branch : Branching α) (s : State α) :
    (run branch s).visits = s.visits + forestNodes branch s.pending := by
  have h := runFuel_node_conservation branch (potential branch.mass s.pending) s
  change (run branch s).visits + forestNodes branch (run branch s).pending = _ at h
  simpa only [run_pending_nil, forestNodes_nil, Nat.add_zero] using h

theorem initial_run_visits (branch : Branching α) (x : α) :
    (run branch (initial x)).visits = (tree branch x).nodeCount := by
  simpa [initial] using run_visits branch (initial x)

theorem run_execution (branch : Branching α) (s : State α) :
    Computation.Trace (transition branch.split) (forestNodes branch s.pending) s (run branch s) := by
  obtain ⟨q, hq, hv⟩ := runFuel_execution branch.split (potential branch.mass s.pending) s
  change (run branch s).visits = s.visits + q at hv
  rw [run_visits] at hv
  have he : forestNodes branch s.pending = q := Nat.add_left_cancel hv
  exact he ▸ hq

theorem initial_run_execution (branch : Branching α) (x : α) :
    Computation.Trace (transition branch.split) (tree branch x).nodeCount
      (initial x) (run branch (initial x)) := by
  simpa [initial] using run_execution branch (initial x)

theorem run_terminal (branch : Branching α) (s : State α) :
    transition branch.split (run branch s) = none := by
  simp [transition, run_pending_nil]

theorem run_after_step (branch : Branching α) (s : State α) (h : s.pending ≠ []) :
    run branch s = run branch (step branch.split s) := by
  have hstep : transition branch.split s = some (step branch.split s) := by
    cases hp : s.pending with
    | nil => exact False.elim (h hp)
    | cons x xs => simp [transition, hp]
  have ht := Computation.Trace.cons hstep (run_execution branch (step branch.split s))
  exact Computation.RunsIn.terminal_unique
    ⟨_, le_rfl, run_execution branch s⟩ ⟨_, le_rfl, ht⟩
    (run_terminal branch s) (run_terminal branch (step branch.split s))

section MeasuredTraversal

/-- Measured callbacks return both their actual result and their event count. -/
abbrev Evaluator (α : Type*) := α → Option (α × α) × ℕ

/-- Count the displayed list cases, Boolean option case, list constructors,
and visit-counter successor, together with the actual callback events.
Counter bookkeeping is instrumentation; these are not primitive-bit costs. -/
def stepM (eval : Evaluator α) (s : State α) : State α × ℕ :=
  match s.pending with
  | [] => (s, 1)
  | x :: rest =>
      let result := eval x
      match result.1 with
      | none => (⟨rest, x :: s.leaves, s.visits + 1⟩, result.2 + 4)
      | some (a, b) => (⟨a :: b :: rest, s.leaves, s.visits + 1⟩, result.2 + 5)

theorem stepM_value (branch : Branching α) (eval : Evaluator α)
    (heval : ∀ x, (eval x).1 = branch.split x) (s : State α) :
    (stepM eval s).1 = step branch.split s := by
  rcases s with ⟨pending, leaves, visits⟩
  cases pending with
  | nil => rfl
  | cons x xs =>
    cases hs : branch.split x <;> simp [stepM, step, heval, hs]

/-- The measured program loops until the worklist is empty. Its termination
measure exists only in the proof and is never stored or computed as fuel. -/
def runM (branch : Branching α) (eval : Evaluator α)
    (heval : ∀ x, (eval x).1 = branch.split x) (s : State α) : State α × ℕ :=
  match hp : s.pending with
  | [] => (s, 1)
  | _ :: _ =>
      let next := stepM eval s
      let result := runM branch eval heval next.1
      (result.1, next.2 + result.2 + 1)
termination_by potential branch.mass s.pending
decreasing_by
  rw [stepM_value branch eval heval]
  apply step_potential_lt
  rw [hp]
  simp

theorem runM_value (branch : Branching α) (eval : Evaluator α)
    (heval : ∀ x, (eval x).1 = branch.split x) (s : State α) :
    (runM branch eval heval s).1 = run branch s := by
  induction s using (measure (fun s : State α => potential branch.mass s.pending)).wf.induction with
  | h s ih =>
    cases hp : s.pending with
    | nil =>
      rw [runM, hp]
      simp [run, hp, runFuel]
    | cons x xs =>
      have hn : s.pending ≠ [] := by rw [hp]; simp
      have hd : potential branch.mass (stepM eval s).1.pending < potential branch.mass s.pending := by
        rw [stepM_value branch eval heval]
        exact step_potential_lt branch s hn
      rw [runM, hp]
      simp only
      rw [ih (stepM eval s).1 hd, stepM_value branch eval heval]
      exact (run_after_step branch s hn).symm

/-- Exact event cost of a specification node, including the worklist's own
case/constructor events. It is defined from the executed callback counts. -/
def nodeEvents (branch : Branching α) (eval : Evaluator α) (x : α) : ℕ :=
  match h : branch.split x with
  | none => (eval x).2 + 5
  | some (a, b) => (eval x).2 + 6 + nodeEvents branch eval a + nodeEvents branch eval b
termination_by branch.mass x
decreasing_by
  · exact (branch.decreases x a b h).1
  · exact (branch.decreases x a b h).2

theorem nodeEvents_none (branch : Branching α) (eval : Evaluator α) (x : α)
    (h : branch.split x = none) : nodeEvents branch eval x = (eval x).2 + 5 := by
  rw [nodeEvents, h]

theorem nodeEvents_some (branch : Branching α) (eval : Evaluator α) (x a b : α)
    (h : branch.split x = some (a, b)) :
    nodeEvents branch eval x = (eval x).2 + 6 +
      nodeEvents branch eval a + nodeEvents branch eval b := by
  rw [nodeEvents, h]

def forestEvents (branch : Branching α) (eval : Evaluator α) (xs : List α) : ℕ :=
  (xs.map (nodeEvents branch eval)).sum

@[simp] theorem forestEvents_nil (branch : Branching α) (eval : Evaluator α) :
    forestEvents branch eval [] = 0 := rfl

@[simp] theorem forestEvents_cons (branch : Branching α) (eval : Evaluator α)
    (x : α) (xs : List α) :
    forestEvents branch eval (x :: xs) = nodeEvents branch eval x + forestEvents branch eval xs := rfl

/-- Exact accumulation over the actual measured traversal. The extra one is
the final empty-worklist inspection. -/
theorem runM_events (branch : Branching α) (eval : Evaluator α)
    (heval : ∀ x, (eval x).1 = branch.split x) (s : State α) :
    (runM branch eval heval s).2 = forestEvents branch eval s.pending + 1 := by
  induction s using (measure (fun s : State α => potential branch.mass s.pending)).wf.induction with
  | h s ih =>
    cases hp : s.pending with
    | nil =>
      rw [runM, hp]
      simp
    | cons x xs =>
      have hn : s.pending ≠ [] := by rw [hp]; simp
      have hd : potential branch.mass (stepM eval s).1.pending < potential branch.mass s.pending := by
        rw [stepM_value branch eval heval]
        exact step_potential_lt branch s hn
      have hrec := ih (stepM eval s).1 hd
      rw [runM, hp]
      simp only
      rw [hrec]
      cases hs : branch.split x with
      | none =>
        have he : (eval x).1 = none := (heval x).trans hs
        simp only [stepM, hp, he, forestEvents_cons, nodeEvents_none branch eval x hs]
        omega
      | some pair =>
        rcases pair with ⟨a, b⟩
        have he : (eval x).1 = some (a, b) := (heval x).trans hs
        simp only [stepM, hp, he, forestEvents_cons, nodeEvents_some branch eval x a b hs]
        omega

theorem nodeEvents_bound (branch : Branching α) (eval : Evaluator α) (P : α → Prop)
    (hclosed : SplitClosed branch.split P) (bound : ℕ)
    (hbound : ∀ x, P x → (eval x).2 ≤ bound) (x : α) (hx : P x) :
    nodeEvents branch eval x ≤ (bound + 6) * (tree branch x).nodeCount := by
  induction x using (measure branch.mass).wf.induction with
  | h x ih =>
    have hc := hbound x hx
    cases hs : branch.split x with
    | none =>
      rw [nodeEvents, hs, tree_none branch x hs]
      simp only [BranchTree.Tree.nodeCount, Nat.mul_one]
      omega
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hd := branch.decreases x a b hs
      have hab := hclosed x a b hx hs
      have ha := ih a hd.1 hab.1
      have hb := ih b hd.2 hab.2
      rw [nodeEvents, hs, tree_some branch x a b hs]
      simp only [BranchTree.Tree.nodeCount]
      calc
        _ ≤ bound + 6 + (bound + 6) * (tree branch a).nodeCount +
            (bound + 6) * (tree branch b).nodeCount := by omega
        _ = _ := by ring

/-- Aggregation theorem for measured operations, distinct from primitive bit
complexity. Concrete use must discharge `hbound` with the callback's proofs. -/
theorem initial_runM_events_bound (branch : Branching α) (eval : Evaluator α)
    (heval : ∀ x, (eval x).1 = branch.split x) (P : α → Prop)
    (hclosed : SplitClosed branch.split P) (bound : ℕ)
    (hbound : ∀ x, P x → (eval x).2 ≤ bound) (x : α) (hx : P x) :
    (runM branch eval heval (initial x)).2 ≤
      (bound + 6) * (run branch (initial x)).visits + 1 := by
  rw [runM_events, initial_run_visits]
  simpa [initial] using Nat.add_le_add_right (nodeEvents_bound branch eval P hclosed bound hbound x hx) 1

end MeasuredTraversal

theorem runFuel_leaves_length_le (split : α → Option (α × α)) (fuel : ℕ)
    (s : State α) (h : s.leaves.length ≤ s.visits) :
    (runFuel split fuel s).leaves.length ≤ (runFuel split fuel s).visits := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simpa [runFuel, hp] using h
    | cons x xs =>
      simp only [runFuel, hp]
      apply ih (step split s)
      cases hs : split x with
      | none => simpa [step, hp, hs] using Nat.succ_le_succ h
      | some pair => simpa [step, hp, hs] using Nat.le_succ_of_le h

theorem initial_run_leaves_length_le_visits (branch : Branching α) (x : α) :
    (run branch (initial x)).leaves.length ≤ (run branch (initial x)).visits :=
  runFuel_leaves_length_le branch.split _ _ (by simp [initial])

/-- Every existing finite binary-tree bound applies to this actual worklist
visit counter after supplying the tree's path bounds. -/
theorem initial_run_visits_le (branch : Branching α) (x : α) (D R : ℕ)
    (hdepth : ∀ p ∈ (tree branch x).paths, p.length ≤ D)
    (hB : ∀ p ∈ (tree branch x).paths, (BranchTree.bPositions p).card ≤ R) :
    (run branch (initial x)).visits ≤
      (D + 1) * ∑ r ∈ Finset.range (R + 1), D.choose r := by
  rw [initial_run_visits]
  exact (tree branch x).nodeCount_le D R hdepth hB

/-- A finite-set semantic refinement of the executable branch operation.
The witness is an actual sunflower choice, not a node-count certificate. -/
def RefinesChoices {n : ℕ} (branch : Branching α) (sem : α → SAT.CNF (Fin n))
    (z : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ x a b, branch.split x = some (a, b) →
    ∃ c : Sparsify.Choice (sem x) z k, sem a = c.child false ∧ sem b = c.child true

def RefinesTerminal {n : ℕ} (branch : Branching α) (sem : α → SAT.CNF (Fin n))
    (z : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ x, branch.split x = none → ∀ d, 2 ≤ d → d ≤ k → Sparsify.FreeAt (sem x) z d

theorem decomposition_shape_cast {n k : ℕ} {z : ℕ → ℕ} {F G : SAT.CNF (Fin n)}
    (h : F = G) (t : Sparsify.Decomposition z k F) :
    (h ▸ t).shape = t.shape := by cases h; rfl

/-- The worklist's specification tree is the shape of a genuine sunflower
decomposition, even when its deterministic enumeration differs from the older
finite-set selector. -/
theorem tree_is_decomposition {n k : ℕ} (branch : Branching α)
    (sem : α → SAT.CNF (Fin n)) (z : ℕ → ℕ)
    (hchoice : RefinesChoices branch sem z k) (hterminal : RefinesTerminal branch sem z k)
    (x : α) : ∃ t : Sparsify.Decomposition z k (sem x), t.shape = tree branch x := by
  induction x using (measure branch.mass).wf.induction with
  | h x ih =>
    cases hs : branch.split x with
    | none =>
      refine ⟨.leaf (sem x) (hterminal x hs), ?_⟩
      rw [tree_none branch x hs]
      rfl
    | some pair =>
      rcases pair with ⟨a, b⟩
      have hdec := branch.decreases x a b hs
      obtain ⟨ta, hta⟩ := ih a hdec.1
      obtain ⟨tb, htb⟩ := ih b hdec.2
      obtain ⟨c, ha, hb⟩ := hchoice x a b hs
      refine ⟨.branch c (ha ▸ ta) (hb ▸ tb), ?_⟩
      simp only [Sparsify.Decomposition.shape, decomposition_shape_cast, hta, htb,
        tree_some branch x a b hs]

/-- The variable-σ node bound applies to the actual worklist visit count once
the executable selector has been refined to concrete sunflower choices. -/
theorem initial_run_visits_quantitative {n k M : ℕ} (branch : Branching α)
    (sem : α → SAT.CNF (Fin n))
    (hchoice : RefinesChoices branch sem (SparsificationConstants.z M) k)
    (hterminal : RefinesTerminal branch sem (SparsificationConstants.z M) k)
    (x : α) (hanti : SunflowerBranch.Antichain (sem x))
    (hM : 2 ≤ M) (hk : 0 < k) (σ : ℝ)
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((run branch (initial x)).visits : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  obtain ⟨t, ht⟩ := tree_is_decomposition branch sem (SparsificationConstants.z M)
    hchoice hterminal x
  rw [initial_run_visits, ← ht]
  exact QuantitativeBranchTree.decomposition_nodeCount_le t hM hk σ hanti hDim hbudget

section MeasuredSelection

variable [DecidableEq α]
open ExecClauseCost ExecSunflowerSearch

/-- Candidate construction with the actual clause-deduplication loop included. -/
def buildCandidatesM (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d : ℕ) :
    List (Candidate α) × ℕ :=
  let unique := dedupClausesM F
  let families := enumerateFixed (z d) unique.1
  let cores := enumerateCoreFamily F
  let pairs := pairLists families.values cores.values
  (pairs.1, unique.2 + families.calls + families.cells + cores.calls + cores.cells + pairs.2)

@[simp] theorem buildCandidatesM_value (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d : ℕ) :
    (buildCandidatesM F z d).1 = candidates F z d := by
  simp [buildCandidatesM, candidates, buildCandidates]

theorem buildCandidatesM_cost (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d : ℕ) :
    (buildCandidatesM F z d).2 = (dedupClausesM F).2 + (buildCandidates F z d).2 := by
  simp [buildCandidatesM, buildCandidates, Nat.add_assoc]

def dedupBudget (m k : ℕ) : ℕ := m * (m * (pairBudget k + 1) + 2) + 1

/-- Includes recursive generation, all candidate checks, and composition events. -/
def searchBudget (m k Z : ℕ) : ℕ :=
  dedupBudget m k + generationBudget (m + 1) k Z +
    (m + 1) ^ (Z + 1) * 2 ^ k * (checkerBudget m m k + 1) + 2

/-- Enlarging the base to `m+1` also handles an empty input list. -/
theorem generationBudget_le_cap (m k r Z : ℕ) (hr : r ≤ Z) :
    generationBudget m k r ≤ generationBudget (m + 1) k Z := by
  unfold generationBudget
  gcongr <;> omega

/-- The measured search calls the measured checker on the generated candidates. -/
def searchAtM (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d : ℕ) :
    Option (Candidate α) × ℕ :=
  let generated := buildCandidatesM F z d
  let found := scanM (checkM F z d) generated.1
  (found.1, generated.2 + found.2 + 1)

@[simp] theorem searchAtM_value (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d : ℕ) :
    (searchAtM F z d).1 = (searchAt F z d).1 := by
  simp [searchAtM, searchAt]

theorem searchAtM_cost_le (F : ExecCNF.Formula α) (z : ℕ → ℕ) (d k Z : ℕ)
    (hF : RawWidthAtMost k F) (hZ : z d ≤ Z) :
    (searchAtM F z d).2 ≤ searchBudget F.length k Z := by
  have hchecks : ∀ c ∈ candidates F z d,
      (checkM F z d c).2 ≤ checkerBudget F.length F.length k := by
    intro c hc
    have hb := candidate_bounds F z d k hF hc
    exact (checkM_cost_le F z d c k hF hb.2.1 hb.2.2.1).trans
      (checkerBudget_mono_s F.length k hb.2.2.2.1)
  have hs := scanM_cost_le (checkM F z d) (candidates F z d)
    (checkerBudget F.length F.length k) hchecks
  have hn : (candidates F z d).length ≤ (F.length + 1) ^ (Z + 1) * 2 ^ k := by
    apply (candidates_length_le F z d k hF).trans
    apply Nat.mul_le_mul_right
    exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hg := (buildCandidates_count_le F z d k hF).trans
    (generationBudget_le_cap F.length k (z d) Z hZ)
  have hu := dedupClausesM_cost_le F k hF
  have hc : (scanM (checkM F z d) (candidates F z d)).2 ≤
      (F.length + 1) ^ (Z + 1) * 2 ^ k *
        (checkerBudget F.length F.length k + 1) + 1 :=
    hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [searchAtM, buildCandidatesM_value, buildCandidatesM_cost]
  change _ ≤ dedupBudget F.length k + _ + _ + 2
  dsimp [dedupBudget]
  omega

/-- Explicit width loop, charging each width and option inspection. -/
def scanWidthsM {β : Type*} (find : ℕ → Option β × ℕ) :
    ℕ → ℕ → Option (ℕ × β) × ℕ
  | _, 0 => (none, 1)
  | start, fuel + 1 =>
      let found := find start
      match found.1 with
      | some c => (some (start, c), found.2 + 2)
      | none =>
          let rest := scanWidthsM find (start + 1) fuel
          (rest.1, found.2 + rest.2 + 2)

@[simp] theorem scanWidthsM_value {β : Type*} (find : ℕ → Option β × ℕ)
    (start fuel : ℕ) :
    (scanWidthsM find start fuel).1 = (scanWidths find start fuel).1 := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    cases hs : (find start).1 <;> simp [scanWidthsM, scanWidths, hs, ih]

theorem scanWidths_value_congr {β : Type*} (find find' : ℕ → Option β × ℕ)
    (heq : ∀ d, (find d).1 = (find' d).1) (start fuel : ℕ) :
    (scanWidths find start fuel).1 = (scanWidths find' start fuel).1 := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    cases hs : (find' start).1 <;> simp [scanWidths, heq, hs, ih]

theorem scanWidthsM_cost_le {β : Type*} (find : ℕ → Option β × ℕ)
    (start fuel bound : ℕ)
    (hbound : ∀ d, start ≤ d → d < start + fuel → (find d).2 ≤ bound) :
    (scanWidthsM find start fuel).2 ≤ fuel * (bound + 2) + 1 := by
  induction fuel generalizing start with
  | zero => simp [scanWidthsM]
  | succ fuel ih =>
    have hf := hbound start le_rfl (by omega)
    have ht := ih (start + 1) (by intro d h₁ h₂; exact hbound d (by omega) (by omega))
    cases hs : (find start).1 <;>
      simp only [scanWidthsM, hs, Nat.succ_mul] <;> omega

/-- All widths are inspected by the measured loop; no search is an atomic event. -/
def selectM (F : ExecCNF.Formula α) (z : ℕ → ℕ) (k : ℕ) :
    Option (ℕ × Candidate α) × ℕ :=
  let found := scanWidthsM (searchAtM F z) 2 (k - 1)
  (found.1, found.2 + 1)

@[simp] theorem selectM_value (F : ExecCNF.Formula α) (z : ℕ → ℕ) (k : ℕ) :
    (selectM F z k).1 = (select F z k).1 := by
  simp only [selectM, scanWidthsM_value, select]
  exact scanWidths_value_congr _ _ (fun d => searchAtM_value F z d) _ _

def selectionBudget (m k Z : ℕ) : ℕ := k * (searchBudget m k Z + 2) + 2

theorem selectM_cost_le (F : ExecCNF.Formula α) (z : ℕ → ℕ) (k Z : ℕ)
    (hF : RawWidthAtMost k F) (hZ : ∀ d, 2 ≤ d → d ≤ k → z d ≤ Z) :
    (selectM F z k).2 ≤ selectionBudget F.length k Z := by
  have h := scanWidthsM_cost_le (searchAtM F z) 2 (k - 1)
    (searchBudget F.length k Z) (by
      intro d hd hdk
      exact searchAtM_cost_le F z d k Z hF (hZ d hd (by omega)))
  have hm := Nat.mul_le_mul_right (searchBudget F.length k Z + 2) (Nat.sub_le k 1)
  dsimp [selectM, selectionBudget]
  omega

/-- Petal lists are built by measured membership filters over every selected clause. -/
def petalsM (c : Candidate α) : ExecCNF.Formula α × ℕ :=
  mapM (fun C => filterM (fun x => notM (containsM x c.2)) C) c.1

@[simp] theorem petalsM_value (c : Candidate α) : (petalsM c).1 = petals c := by
  simp [petalsM, petals]

def petalsBudget (m k : ℕ) : ℕ := m * (k * (2*k+3) + 2) + 1

theorem petalsM_cost_le (c : Candidate α) (k : ℕ)
    (hG : RawWidthAtMost k c.1) (hH : c.2.length ≤ k) :
    (petalsM c).2 ≤ petalsBudget c.1.length k := by
  apply mapM_cost_le
  intro C hC
  have h := filterM_cost_le (fun x => notM (containsM x c.2)) C (2*k+2) (by
    intro x hx
    have ht := containsM_cost_le x c.2
    dsimp [ExecClauseCost.notM]
    omega)
  apply h.trans
  have hc := hG C hC
  gcongr

@[simp] theorem petals_length (c : Candidate α) : (petals c).length = c.1.length := by
  simp [petals]

theorem petals_width (c : Candidate α) (k : ℕ) (hG : RawWidthAtMost k c.1) :
    RawWidthAtMost k (petals c) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  exact (List.length_filter_le _ _).trans (hG D hD)

theorem childA_raw_width (F : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (P : ExecCNF.Formula α) (k : ℕ) (hF : RawWidthAtMost k F) (hH : H.length ≤ k) :
    RawWidthAtMost k (ExecCNF.childA F H P) := by
  intro C hC
  have hc := ExecCNF.absorb_subset _ hC
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hH
  · exact hF C (List.mem_filter.mp hc).1

theorem childB_raw_width (F : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (P : ExecCNF.Formula α) (k : ℕ) (hF : RawWidthAtMost k F)
    (hP : RawWidthAtMost k P) : RawWidthAtMost k (ExecCNF.childB F H P) := by
  intro C hC
  have hc := ExecCNF.absorb_subset _ hC
  rcases List.mem_append.mp hc with hc | hc
  · exact hF C (List.mem_filter.mp hc).1
  · exact hP C hc

theorem selected_candidate_bounds (F : ExecCNF.Formula α) (z : ℕ → ℕ) (k : ℕ)
    (hF : RawWidthAtMost k F) {d : ℕ} {c : Candidate α}
    (hs : (select F z k).1 = some (d,c)) :
    RawWidthAtMost k c.1 ∧ c.2.length ≤ k ∧ c.1.length ≤ F.length := by
  obtain ⟨_, _, hsearch, _⟩ := scanWidths_some (searchAt F z) 2 (k-1) hs
  have hc := (scan_some (check F z d) (candidates F z d) hsearch).1
  have hb := candidate_bounds F z d k hF hc
  exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2.1⟩

end MeasuredSelection

section ExecutableSelection

variable {n : ℕ}

abbrev Formula (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

/-- A list-only pass removing repeated literals from each clause. -/
def cleanLiterals (F : Formula n) : Formula n := F.map ExecCNF.dedupLiterals

@[simp] theorem cleanLiterals_set (F : Formula n) :
    ExecCNF.formulaSet (cleanLiterals F) = ExecCNF.formulaSet F := by
  ext C
  simp only [ExecCNF.mem_formulaSet, cleanLiterals, List.mem_map]
  constructor
  · rintro ⟨D, ⟨E, hE, rfl⟩, hD⟩
    exact ⟨E, hE, by simpa using hD⟩
  · rintro ⟨D, hD, hC⟩
    exact ⟨ExecCNF.dedupLiterals D, ⟨D, hD, rfl⟩, by simpa using hC⟩

theorem cleanLiterals_raw_width (F : Formula n) (k : ℕ)
    (hwidth : SAT.WidthAtMost k (ExecCNF.formulaSet F)) :
    ∀ C ∈ cleanLiterals F, C.length ≤ k := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  rw [ExecSunflowerSearch.dedupLiterals_length]
  exact hwidth _ (ExecCNF.mem_formulaSet.mpr ⟨D, hD, rfl⟩)

/-- Reconstruct the finite-set branch witness from the actual executable
selector's successful Boolean checks and minimum-width scan. -/
def choiceOfSelected (F : Formula n) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) {d : ℕ}
    {c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))}
    (h : (ExecSunflowerSearch.select F z k).1 = some (d, c)) :
    Sparsify.Choice (ExecCNF.formulaSet F) z k := by
  have hs := ExecSunflowerSearch.select_some F z k hz h
  have hg := hs.2.2.1
  let s := SunflowerBranch.Sunflower.ofClauses
    (ExecCNF.formulaSet c.1) (ExecCNF.clauseSet c.2) d hg.2.2.1
    (by simpa only [hg.2.1] using hz d hs.1) hg.2.2.2.1.1
    hg.2.2.2.1.2 hg.2.2.2.2
  refine ⟨d, hs.1, hs.2.1, s, ?_, ?_, ?_⟩
  · simpa only [s, SunflowerBranch.Sunflower.ofClauses_selected] using hg.1
  · simpa only [s, SunflowerBranch.Sunflower.ofClauses,
      SunflowerBranch.petalFamily_card hg.2.2.2.1.1] using hg.2.1
  · exact hs.2.2.2

@[simp] theorem choiceOfSelected_core (F : Formula n) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) {d : ℕ}
    {c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))}
    (h : (ExecSunflowerSearch.select F z k).1 = some (d, c)) :
    (choiceOfSelected F z k hz h).flower.core = ExecCNF.clauseSet c.2 := rfl

@[simp] theorem choiceOfSelected_petals (F : Formula n) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) {d : ℕ}
    {c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))}
    (h : (ExecSunflowerSearch.select F z k).1 = some (d, c)) :
    (choiceOfSelected F z k hz h).flower.petals =
      SunflowerBranch.petalFamily (ExecCNF.formulaSet c.1) (ExecCNF.clauseSet c.2) := rfl

/-- Actual executable children, with only literal deduplication after the
branch. No extra tautology deletion changes the finite-set child identity. -/
def children (F : Formula n) (c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))) :
    Formula n × Formula n :=
  (cleanLiterals (ExecCNF.childA F c.2 (ExecSunflowerSearch.petals c)),
   cleanLiterals (ExecCNF.childB F c.2 (ExecSunflowerSearch.petals c)))

theorem children_left_set (F : Formula n) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) {d : ℕ}
    {c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))}
    (h : (ExecSunflowerSearch.select F z k).1 = some (d, c)) :
    ExecCNF.formulaSet (children F c).1 = (choiceOfSelected F z k hz h).child false := by
  simp only [children, cleanLiterals_set, ExecCNF.childA_set,
    Sparsify.Choice.child, Bool.false_eq_true, ite_false, choiceOfSelected_core,
    choiceOfSelected_petals, ExecSunflowerSearch.petals_set, SunflowerBranch.petalFamily]

theorem children_right_set (F : Formula n) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) {d : ℕ}
    {c : ExecSunflowerSearch.Candidate (SAT.Literal (Fin n))}
    (h : (ExecSunflowerSearch.select F z k).1 = some (d, c)) :
    ExecCNF.formulaSet (children F c).2 = (choiceOfSelected F z k hz h).child true := by
  simp only [children, cleanLiterals_set, ExecCNF.childB_set,
    Sparsify.Choice.child, ite_true, choiceOfSelected_core,
    choiceOfSelected_petals, ExecSunflowerSearch.petals_set, SunflowerBranch.petalFamily]

/-- The actual executable selector and child constructors used by the loop. -/
def splitFormula (z : ℕ → ℕ) (k : ℕ) (F : Formula n) : Option (Formula n × Formula n) :=
  match (ExecSunflowerSearch.select F z k).1 with
  | none => none
  | some (_, c) => some (children F c)

theorem splitFormula_none_iff (z : ℕ → ℕ) (k : ℕ) (F : Formula n) :
    splitFormula z k F = none ↔ (ExecSunflowerSearch.select F z k).1 = none := by
  unfold splitFormula
  cases (ExecSunflowerSearch.select F z k).1 <;> simp

theorem splitFormula_some (z : ℕ → ℕ) (k : ℕ) (F A B : Formula n)
    (h : splitFormula z k F = some (A, B)) :
    ∃ d c, (ExecSunflowerSearch.select F z k).1 = some (d, c) ∧
      A = (children F c).1 ∧ B = (children F c).2 := by
  cases hs : (ExecSunflowerSearch.select F z k).1 with
  | none => simp [splitFormula, hs] at h
  | some pair =>
    rcases pair with ⟨d, c⟩
    have he : children F c = (A, B) := by simpa [splitFormula, hs] using h
    exact ⟨d, c, rfl, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- The mass is computed by explicit clause/literal deduplication and list
lengths. Its equality with mathematical literal mass is proved separately. -/
def formulaMass (F : Formula n) : ℕ := ExecCNF.mass F

@[simp] theorem formulaMass_eq (F : Formula n) :
    formulaMass F = SunflowerBranch.literalMass (ExecCNF.formulaSet F) :=
  ExecCNF.mass_eq_literalMass F

/-- The generic engine is now instantiated by the actual list search. -/
def executableBranching (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) : Branching (Formula n) where
  split := splitFormula z k
  mass := formulaMass
  decreases := by
    intro F A B h
    obtain ⟨d, c, hs, rfl, rfl⟩ := splitFormula_some z k F A B h
    constructor
    · rw [formulaMass_eq, formulaMass_eq]
      rw [children_left_set F z k hz hs]
      exact (choiceOfSelected F z k hz hs).child_mass_lt false
    · rw [formulaMass_eq, formulaMass_eq]
      rw [children_right_set F z k hz hs]
      exact (choiceOfSelected F z k hz hs).child_mass_lt true

theorem executable_refinesChoices (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    RefinesChoices (executableBranching (n := n) z k hz) ExecCNF.formulaSet z k := by
  intro F A B h
  obtain ⟨d, c, hs, rfl, rfl⟩ := splitFormula_some z k F A B h
  exact ⟨choiceOfSelected F z k hz hs, children_left_set F z k hz hs,
    children_right_set F z k hz hs⟩

theorem executable_refinesTerminal (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    RefinesTerminal (executableBranching (n := n) z k hz) ExecCNF.formulaSet z k := by
  intro F h
  exact (ExecSunflowerSearch.select_none_iff F z k hz).mp
    ((splitFormula_none_iff z k F).mp h)

theorem executable_sound (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    SplitSound (executableBranching (n := n) z k hz).split
      (fun F => SAT.Satisfiable (ExecCNF.formulaSet F)) := by
  intro F A B h
  obtain ⟨c, ha, hb⟩ := executable_refinesChoices z k hz F A B h
  change SAT.Satisfiable (ExecCNF.formulaSet F) ↔
    SAT.Satisfiable (ExecCNF.formulaSet A) ∨ SAT.Satisfiable (ExecCNF.formulaSet B)
  rw [ha, hb]
  exact SunflowerBranch.satisfiable_children_iff _ c.flower.core c.flower.petals c.present

theorem executable_width_closed (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    SplitClosed (executableBranching (n := n) z k hz).split
      (fun F => SAT.WidthAtMost k (ExecCNF.formulaSet F)) := by
  intro F A B hF h
  obtain ⟨c, ha, hb⟩ := executable_refinesChoices z k hz F A B h
  change SAT.WidthAtMost k (ExecCNF.formulaSet A) ∧ SAT.WidthAtMost k (ExecCNF.formulaSet B)
  rw [ha, hb]
  exact ⟨c.child_width false hF, c.child_width true hF⟩

theorem semantic_width_of_raw (F : Formula n) (k : ℕ)
    (h : ExecSunflowerSearch.RawWidthAtMost k F) : SAT.WidthAtMost k (ExecCNF.formulaSet F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact (List.toFinset_card_le D).trans (h D hD)

theorem executable_raw_width_closed (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    SplitClosed (executableBranching (n := n) z k hz).split
      (ExecSunflowerSearch.RawWidthAtMost k) := by
  intro F A B hF h
  have hw := executable_width_closed z k hz F A B (semantic_width_of_raw F k hF) h
  obtain ⟨d, c, hs, rfl, rfl⟩ := splitFormula_some z k F A B h
  constructor
  · apply cleanLiterals_raw_width
    simpa only [children, cleanLiterals_set] using hw.1
  · apply cleanLiterals_raw_width
    simpa only [children, cleanLiterals_set] using hw.2

/-- Normalize once at input. The last cleanup is semantically redundant but
makes the raw-width invariant explicit at the worklist interface. -/
def normalizedInput (F : Formula n) : Formula n :=
  cleanLiterals (ExecCNF.normalize SAT.Literal.negate F)

@[simp] theorem normalizedInput_set (F : Formula n) :
    ExecCNF.formulaSet (normalizedInput F) = SAT.normalize (ExecCNF.formulaSet F) := by
  simp only [normalizedInput, cleanLiterals_set, ExecCNF.normalize_set]

/-- Actual finite list-CNF depth-first sparsification. -/
def execute (z : ℕ → ℕ) (k : ℕ) (hz : ∀ d, 2 ≤ d → 2 ≤ z d)
    (F : Formula n) : State (Formula n) :=
  run (executableBranching z k hz) (initial (normalizedInput F))

theorem execute_pending_nil (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) : (execute z k hz F).pending = [] :=
  run_pending_nil _ _

theorem execute_correct (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) :
    SAT.Satisfiable (ExecCNF.formulaSet F) ↔
      ∃ G ∈ (execute z k hz F).leaves, SAT.Satisfiable (ExecCNF.formulaSet G) := by
  have h := initial_run_correct (executableBranching z k hz)
    (fun G => SAT.Satisfiable (ExecCNF.formulaSet G))
    (executable_sound z k hz) (normalizedInput F)
  rw [normalizedInput_set] at h
  exact (SAT.satisfiable_normalize _).symm.trans h

/-- Pointwise assignment semantics: the output formulas' disjunction equals
the input formula, before existentially quantifying over assignments. -/
theorem execute_models (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) (a : SAT.Assignment (Fin n)) :
    SAT.CNF.eval a (ExecCNF.formulaSet F) = true ↔
      ∃ G ∈ (execute z k hz F).leaves, SAT.CNF.eval a (ExecCNF.formulaSet G) = true := by
  have hsound : SplitSound (executableBranching (n := n) z k hz).split
      (fun G => SAT.CNF.eval a (ExecCNF.formulaSet G) = true) := by
    intro X A B h
    obtain ⟨c, hA, hB⟩ := executable_refinesChoices z k hz X A B h
    change SAT.CNF.eval a (ExecCNF.formulaSet X) = true ↔
      SAT.CNF.eval a (ExecCNF.formulaSet A) = true ∨ SAT.CNF.eval a (ExecCNF.formulaSet B) = true
    rw [hA, hB]
    exact SunflowerBranch.eval_children_iff a _ c.flower.core c.flower.petals c.present
  have h := initial_run_correct (executableBranching z k hz)
    (fun G => SAT.CNF.eval a (ExecCNF.formulaSet G) = true) hsound (normalizedInput F)
  simpa only [execute, normalizedInput_set, SAT.eval_normalize, ListOr] using h

theorem execute_terminal_leaves (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) :
    ∀ G ∈ (execute z k hz F).leaves,
      ∀ d, 2 ≤ d → d ≤ k → Sparsify.FreeAt (ExecCNF.formulaSet G) z d := by
  intro G hG
  exact executable_refinesTerminal z k hz G
    (initial_run_leaves_terminal (executableBranching z k hz) (normalizedInput F) G hG)

theorem execute_width (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n)
    (hF : SAT.WidthAtMost k (ExecCNF.formulaSet F)) :
    ∀ G ∈ (execute z k hz F).leaves, SAT.WidthAtMost k (ExecCNF.formulaSet G) := by
  apply initial_run_leaves_invariant (executableBranching z k hz)
    (fun G => SAT.WidthAtMost k (ExecCNF.formulaSet G)) (executable_width_closed z k hz)
  rw [normalizedInput_set]
  exact SAT.widthAtMost_of_subset (SAT.normalize_subset _) hF

theorem execute_raw_width (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n)
    (hF : SAT.WidthAtMost k (ExecCNF.formulaSet F)) :
    ∀ G ∈ (execute z k hz F).leaves, ExecSunflowerSearch.RawWidthAtMost k G := by
  apply initial_run_leaves_invariant (executableBranching z k hz)
    (ExecSunflowerSearch.RawWidthAtMost k) (executable_raw_width_closed z k hz)
  apply cleanLiterals_raw_width
  rw [ExecCNF.normalize_set]
  exact SAT.widthAtMost_of_subset (SAT.normalize_subset _) hF

theorem execute_execution (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : Formula n) :
    Computation.Trace (transition (splitFormula z k)) (execute z k hz F).visits
      (initial (normalizedInput F)) (execute z k hz F) := by
  have h := initial_run_execution (executableBranching z k hz) (normalizedInput F)
  rw [← initial_run_visits] at h
  exact h

theorem execute_visits_quantitative (M k : ℕ) (hM : 2 ≤ M) (hk : 0 < k)
    (σ : ℝ) (F : Formula n)
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((execute (SparsificationConstants.z M) k
      (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd) F).visits : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply initial_run_visits_quantitative
    (executableBranching (SparsificationConstants.z M) k
      (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd))
    ExecCNF.formulaSet (executable_refinesChoices _ _ _) (executable_refinesTerminal _ _ _)
    (normalizedInput F) ?_ hM hk σ hDim hbudget
  rw [normalizedInput_set]
  exact SunflowerBranch.antichain_absorb _

theorem execute_occurrence (M k : ℕ) (hM : 2 ≤ M) (F : Formula n)
    (hF : SAT.WidthAtMost k (ExecCNF.formulaSet F)) :
    ∀ G ∈ (execute (SparsificationConstants.z M) k
      (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd) F).leaves,
      SAT.OccurrenceAtMost (SparsificationConstants.occurrenceCap M k) (ExecCNF.formulaSet G) := by
  intro G hG
  apply Sunflower.terminal_occurrenceAtMost _ M k hM
  · exact execute_width _ _ _ F hF G hG
  · exact execute_terminal_leaves _ _ _ F G hG

theorem execute_leaves_length_quantitative (M k : ℕ) (hM : 2 ≤ M) (hk : 0 < k)
    (σ : ℝ) (F : Formula n)
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((execute (SparsificationConstants.z M) k
      (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd) F).leaves.length : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply le_trans ?_ (execute_visits_quantitative M k hM hk σ F hDim hbudget)
  exact_mod_cast initial_run_leaves_length_le_visits
    (executableBranching (SparsificationConstants.z M) k
      (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd)) (normalizedInput F)

end ExecutableSelection

end SubexponentialSAT.ExecSparsifyWorklist

end OAI.Algorithms
