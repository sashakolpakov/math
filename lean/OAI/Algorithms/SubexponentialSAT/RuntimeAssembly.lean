import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.ExponentArithmetic
import OAI.Algorithms.SubexponentialSAT.SmallInputs
import OAI.Algorithms.SubexponentialSAT.MonomialCount
import OAI.Algorithms.SubexponentialSAT.CosetCardinality
import OAI.Algorithms.SubexponentialSAT.Interfaces
import OAI.Algorithms.SubexponentialSAT.SymbolicCost

namespace OAI.Algorithms

/-!
# From explicit phase budgets to a primitive-machine runtime

The numerical theorems charge initialization, every sparsification node, and
five separate phases of every leaf.  The execution bridge additionally requires
actual traces of one fixed primitive bit machine.  No machine satisfying these
certificates is constructed here.  In particular `ImplementationCertificates`
is an explicit collection of open implementation obligations, not a theorem.
-/

namespace SubexponentialSAT.RuntimeAssembly

noncomputable section

open _root_.OAI.Algorithms.SubexponentialSAT.Computation

/-- The five separately charged phases at a sparsification leaf.  `inner`
means symbolic moment computation on a large input and exhaustive search on a
small input.  Arithmetic costs are numbers of primitive-machine transitions. -/
structure LeafWork where
  tables : ℕ
  layout : ℕ
  inner : ℕ
  interpolation : ℕ
  output : ℕ

def LeafWork.schedule (w : LeafWork) : List ℕ :=
  [w.tables, w.layout, w.inner, w.interpolation, w.output]

def LeafWork.total (w : LeafWork) : ℕ := w.schedule.sum

/-- The list `tree` charges all visited nodes, including internal nodes.
`startup` includes parsing/normalization and construction of fixed objects. -/
structure Work where
  startup : ℕ
  tree : List ℕ
  leaves : List LeafWork

def Work.total (w : Work) : ℕ :=
  w.startup + w.tree.sum + (w.leaves.map LeafWork.total).sum

def Work.schedule (w : Work) : List ℕ :=
  w.startup :: (w.tree ++ w.leaves.flatMap LeafWork.schedule)

theorem sum_leaf_schedules (ws : List LeafWork) :
    (ws.flatMap LeafWork.schedule).sum = (ws.map LeafWork.total).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, LeafWork.total, ih]

theorem Work.sum_schedule (w : Work) : w.schedule.sum = w.total := by
  simp [Work.schedule, Work.total, sum_leaf_schedules, Nat.add_assoc]

/-- An actual run through a finite sequence of bounded phases.  No transition
of `step` is replaced by a semantic oracle or a unit-cost arithmetic command. -/
inductive ScheduledRun {α : Type*} (step : α → Option α) :
    List ℕ → α → α → Prop
  | nil (a : α) : ScheduledRun step [] a a
  | cons {cost : ℕ} {costs : List ℕ} {a b c : α} :
      RunsIn step cost a b → ScheduledRun step costs b c →
      ScheduledRun step (cost :: costs) a c

theorem ScheduledRun.total {α : Type*} {step : α → Option α}
    {costs : List ℕ} {a b : α} (h : ScheduledRun step costs a b) :
    RunsIn step costs.sum a b := by
  induction h with
  | nil a => exact RunsIn.refl step a
  | cons first rest ih => exact first.trans ih

/-- A genuine primitive-machine execution, split into the charged phases.
The choice of one machine is outside the input quantifier in the final bridge. -/
structure PipelineExecution (machine : PrimitiveMachine) {n : ℕ}
    (F : SAT.CNF (Fin n)) (answer : Bool) (w : Work) where
  terminal : machine.Cfg
  phases : ScheduledRun machine.step w.schedule
    (machine.init (Encoding.encodeCNF F)) terminal
  halted : terminal.state = .inl answer

theorem PipelineExecution.outputs {machine : PrimitiveMachine} {n : ℕ}
    {F : SAT.CNF (Fin n)} {answer : Bool} {w : Work}
    (h : PipelineExecution machine F answer w) :
    machine.OutputsInTime (Encoding.encodeCNF F) answer w.total := by
  refine ⟨h.terminal, ?_, h.halted⟩
  simpa only [Work.sum_schedule] using h.phases.total

/-- The semantic obligations are stated at the finite reduction and leaf-test
level, rather than assuming correctness of the whole solver.  The number of
semantic leaves agrees with the number whose work is charged. -/
structure ReductionCertificate {n : ℕ} (F : SAT.CNF (Fin n))
    (answer : Bool) (w : Work) where
  leaves : List (SAT.CNF (Fin n))
  test : SAT.CNF (Fin n) → Bool
  cover : SAT.Satisfiable F ↔ ∃ G ∈ leaves, SAT.Satisfiable G
  leaf_correct : ∀ G ∈ leaves, test G = true ↔ SAT.Satisfiable G
  output : answer = (Interfaces.scan test leaves).1
  leaf_count : leaves.length = w.leaves.length

theorem ReductionCertificate.correct {n : ℕ} {F : SAT.CNF (Fin n)}
    {answer : Bool} {w : Work} (h : ReductionCertificate F answer w) :
    answer = true ↔ SAT.Satisfiable F := by
  rw [h.output, Interfaces.scan_accepts_iff, h.cover]
  constructor
  · rintro ⟨G, hG, ht⟩
    exact ⟨G, hG, (h.leaf_correct G hG).mp ht⟩
  · rintro ⟨G, hG, ht⟩
    exact ⟨G, hG, (h.leaf_correct G hG).mpr ht⟩

/-- A common polynomial envelope may dominate finitely many different phase
polynomials.  Its coefficient and degree must be fixed before the input. -/
def polynomial (C : ℝ) (d L : ℕ) : ℝ := C * ((L : ℝ) + 1) ^ d

def treeExponential (n : ℕ) : ℝ := (2 : ℝ) ^ ((n : ℝ) / 32)

theorem one_le_polynomial {C : ℝ} (hC : 1 ≤ C) (d L : ℕ) :
    1 ≤ polynomial C d L := by
  have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hbase)

/-- Transfers variable-count polynomial overhead to the explicit input length
using the concrete encoder's proved length bound. -/
theorem polynomial_variables_le_input {C : ℝ} (hC : 0 ≤ C) (d : ℕ)
    {n : ℕ} (F : SAT.CNF (Fin n)) :
    polynomial C d n ≤ polynomial C d (Encoding.formulaBitLength F) := by
  have hlen : (n : ℝ) ≤ (Encoding.formulaBitLength F : ℝ) := by
    exact_mod_cast Encoding.numVariables_le_formulaBitLength F
  apply mul_le_mul_of_nonneg_left _ hC
  exact pow_le_pow_left₀ (by positivity) (by linarith) d

theorem one_le_treeExponential (n : ℕ) : 1 ≤ treeExponential n := by
  apply Real.one_le_rpow (by norm_num)
  positivity

theorem one_le_fieldCost {p : ℝ} (hp : 1 ≤ p) (D : ℕ) :
    1 ≤ ExponentArithmetic.fieldCost p (D : ℝ) := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow hp (by positivity)
  · exact Real.one_le_rpow (by norm_num) (by positivity)

/-- Exact product of the moment-index count, the two coset-enumeration
counts, and a supplied dense arithmetic count.  This is a loop count, not
a primitive-machine runtime assertion. -/
def rawSymbolicWork (Q operations p D d0 d1 denseCost : ℕ) : ℕ :=
  Q * Fintype.card (MonomialCount.RetainedX D) *
    (p ^ (D - d0 - d1) * (p ^ d0 + p ^ d1)) * operations * denseCost

/-- Combines actual retained-monomial cardinality with the coset loop bound.
`denseCost` must be supplied by a proved arithmetic-loop count. -/
theorem rawSymbolicWork_le {Q operations p D d0 d1 denseCost a : ℕ}
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1)
    (hdense : denseCost ≤ a * Fintype.card (MonomialCount.RetainedX D) ^ 4) :
    rawSymbolicWork Q operations p D d0 d1 denseCost ≤
      2 * (Q * operations * a) * p ^ (3 * D / 4) * 2 ^ (128 * D) := by
  have hi := CosetCardinality.iteration_bound p D d0 d1 hp hdims hd0 hd1
  have hm := MonomialCount.card_retainedX_pow_five_le_budget D hD
  calc
    rawSymbolicWork Q operations p D d0 d1 denseCost ≤
        Q * Fintype.card (MonomialCount.RetainedX D) *
          (p ^ (D - d0 - d1) * (p ^ d0 + p ^ d1)) * operations *
          (a * Fintype.card (MonomialCount.RetainedX D) ^ 4) :=
      Nat.mul_le_mul_left _ hdense
    _ = (Q * operations * a) *
        ((p ^ (D - d0 - d1) * (p ^ d0 + p ^ d1)) *
          Fintype.card (MonomialCount.RetainedX D) ^ 5) := by ring
    _ ≤ (Q * operations * a) * ((2 * p ^ (3 * D / 4)) * 2 ^ (128 * D)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hi hm)
    _ = 2 * (Q * operations * a) * p ^ (3 * D / 4) * 2 ^ (128 * D) := by ring

theorem rawSymbolicWork_le_real {Q operations p D d0 d1 denseCost a : ℕ}
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1)
    (hdense : denseCost ≤ a * Fintype.card (MonomialCount.RetainedX D) ^ 4) :
    (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) ≤
      2 * (Q * operations * a : ℕ) * ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) := by
  have hnat := rawSymbolicWork_le (Q := Q) (operations := operations)
    hp hD hdims hd0 hd1 hdense
  have hcast : (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) ≤
      2 * (Q * operations * a : ℕ) * (p : ℝ) ^ (3 * D / 4) *
        (2 : ℝ) ^ (128 * D) := by exact_mod_cast hnat
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdiv : ((3 * D / 4 : ℕ) : ℝ) ≤ 3 * (D : ℝ) / 4 := by
    have hm : ((3 * D / 4 : ℕ) : ℝ) * 4 ≤ 3 * (D : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (3 * D) 4
    linarith
  have hpow : (p : ℝ) ^ (3 * D / 4) ≤ (p : ℝ) ^ (3 * (D : ℝ) / 4) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hpR hdiv
  have htwo : (2 : ℝ) ^ (128 * D) = (2 : ℝ) ^ (128 * (D : ℝ)) := by
    rw [← Real.rpow_natCast]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) ≤
        2 * (Q * operations * a : ℕ) * (p : ℝ) ^ (3 * D / 4) *
          (2 : ℝ) ^ (128 * D) := hcast
    _ ≤ 2 * (Q * operations * a : ℕ) * (p : ℝ) ^ (3 * (D : ℝ) / 4) *
          (2 : ℝ) ^ (128 * D) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity)
    _ = 2 * (Q * operations * a : ℕ) *
        ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) := by
      rw [htwo]
      unfold ExponentArithmetic.fieldCost
      ring

/-- The missing bridge from scalar/index loop steps to primitive bit steps
is stated explicitly in `hsteps`. The polynomial certificate also charges
the number of points, ring operations per iteration, and dense-loop overhead. -/
theorem inner_steps_le_of_dense_loops
    {Q operations p D d0 d1 denseCost a steps : ℕ} {bitCost P : ℝ}
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1)
    (hdense : denseCost ≤ a * Fintype.card (MonomialCount.RetainedX D) ^ 4)
    (hbit : 0 ≤ bitCost)
    (hsteps : (steps : ℝ) ≤ bitCost *
      (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ))
    (hpoly : bitCost * (Q * operations * a : ℕ) ≤ P) :
    (steps : ℝ) ≤ 2 * P * ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) := by
  have hraw := rawSymbolicWork_le_real (Q := Q) (operations := operations)
    hp hD hdims hd0 hd1 hdense
  have hf : 0 ≤ ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) := by
    unfold ExponentArithmetic.fieldCost
    positivity
  calc
    (steps : ℝ) ≤ bitCost * (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) := hsteps
    _ ≤ bitCost * (2 * (Q * operations * a : ℕ) *
        ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ)) :=
      mul_le_mul_of_nonneg_left hraw hbit
    _ = 2 * (bitCost * (Q * operations * a : ℕ)) *
        ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) := by ring
    _ ≤ 2 * P * ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by norm_num)) hf

/-- A common event budget for either instrumented dense multiplication or
addition on the actual retained coefficient slots. -/
def denseArithmeticEvents (D : ℕ) : ℕ :=
  max (SymbolicCost.denseCost (Fintype.card (MonomialCount.RetainedMonomial D)))
    (SymbolicCost.denseAddCost (Fintype.card (MonomialCount.RetainedMonomial D)))

theorem denseArithmeticEvents_le (D : ℕ) :
    denseArithmeticEvents D ≤ SymbolicCost.symbolicFactor D *
      Fintype.card (MonomialCount.RetainedX D) ^ 4 :=
  max_le (SymbolicCost.denseCost_retained_le D) (SymbolicCost.denseAddCost_retained_le D)

/-- No symbolic-arithmetic size bound is assumed here: it is supplied by
the instrumented list recursions in `SymbolicCost` and the retained-slot count. -/
theorem instrumented_symbolic_work_le_real {Q operations p D d0 d1 : ℕ}
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1) :
    (rawSymbolicWork Q operations p D d0 d1 (denseArithmeticEvents D) : ℝ) ≤
      2 * (Q * operations * SymbolicCost.symbolicFactor D : ℕ) *
        ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) :=
  rawSymbolicWork_le_real hp hD hdims hd0 hd1 (denseArithmeticEvents_le D)

/-- The numerical obligations, intentionally separated from trace existence.
There is no final `2^(0.9*n)` bound among the assumptions.  The inner bound
allows the explicit factor two in the two separated sums. -/
structure WorkBounds (P E W : ℝ) (w : Work) : Prop where
  startup : (w.startup : ℝ) ≤ P
  node_count : (w.tree.length : ℝ) ≤ P * E
  node_work : ∀ t ∈ w.tree, (t : ℝ) ≤ P
  leaf_count : w.leaves.length ≤ w.tree.length
  tables : ∀ v ∈ w.leaves, (v.tables : ℝ) ≤ P
  layout : ∀ v ∈ w.leaves, (v.layout : ℝ) ≤ P
  inner : ∀ v ∈ w.leaves, (v.inner : ℝ) ≤ 2 * P * W
  interpolation : ∀ v ∈ w.leaves, (v.interpolation : ℝ) ≤ P
  output : ∀ v ∈ w.leaves, (v.output : ℝ) ≤ P

theorem sum_cast_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ)
    (B : ℝ) (h : ∀ x ∈ xs, (f x : ℝ) ≤ B) :
    ((xs.map f).sum : ℝ) ≤ (xs.length : ℝ) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, List.length_cons,
        Nat.cast_one]
      nlinarith

/-- A local primitive simulation can supply the symbolic bit bound without
assuming a bound on the whole symbolic phase: each listed scalar/index event
has its own primitive trace and bounded cost. The number of those events is
bounded by the finite dense-loop count. -/
theorem symbolic_schedule_bit_bound
    {Q operations p D d0 d1 denseCost a : ℕ} {bitCost P : ℝ}
    (costs : List ℕ)
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1)
    (hdense : denseCost ≤ a * Fintype.card (MonomialCount.RetainedX D) ^ 4)
    (hbit : 0 ≤ bitCost)
    (hcount : costs.length ≤ rawSymbolicWork Q operations p D d0 d1 denseCost)
    (hevent : ∀ t ∈ costs, (t : ℝ) ≤ bitCost)
    (hpoly : bitCost * (Q * operations * a : ℕ) ≤ P) :
    (costs.sum : ℝ) ≤ 2 * P * ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) := by
  have hsum : (costs.sum : ℝ) ≤ (costs.length : ℝ) * bitCost := by
    simpa using sum_cast_le_length_mul costs id bitCost hevent
  have hcountR : (costs.length : ℝ) ≤
      (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) := by
    exact_mod_cast hcount
  apply inner_steps_le_of_dense_loops hp hD hdims hd0 hd1 hdense hbit _ hpoly
  calc
    (costs.sum : ℝ) ≤ (costs.length : ℝ) * bitCost := hsum
    _ ≤ (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) * bitCost :=
      mul_le_mul_of_nonneg_right hcountR hbit
    _ = bitCost * (rawSymbolicWork Q operations p D d0 d1 denseCost : ℝ) := by ring

theorem symbolic_schedule_has_bounded_run
    {machine : PrimitiveMachine} {start finish : machine.Cfg}
    {Q operations p D d0 d1 denseCost a : ℕ} {bitCost P : ℝ}
    (costs : List ℕ) (execution : ScheduledRun machine.step costs start finish)
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1)
    (hdense : denseCost ≤ a * Fintype.card (MonomialCount.RetainedX D) ^ 4)
    (hbit : 0 ≤ bitCost)
    (hcount : costs.length ≤ rawSymbolicWork Q operations p D d0 d1 denseCost)
    (hevent : ∀ t ∈ costs, (t : ℝ) ≤ bitCost)
    (hpoly : bitCost * (Q * operations * a : ℕ) ≤ P) :
    ∃ time : ℕ, RunsIn machine.step time start finish ∧
      (time : ℝ) ≤ 2 * P * ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) :=
  ⟨costs.sum, execution.total,
    symbolic_schedule_bit_bound costs hp hD hdims hd0 hd1 hdense hbit hcount hevent hpoly⟩

/-- Complete local cost bridge using the proved dense-arithmetic event count.
The still-required hypotheses are the actual primitive traces, bounded cost
of each scalar/index/list event, a count of those events, and a polynomial
envelope for the remaining factors. -/
theorem instrumented_symbolic_has_bounded_run
    {machine : PrimitiveMachine} {start finish : machine.Cfg}
    {Q operations p D d0 d1 : ℕ} {bitCost P : ℝ}
    (costs : List ℕ) (execution : ScheduledRun machine.step costs start finish)
    (hp : 0 < p) (hD : 1 ≤ D) (hdims : d0 + d1 ≤ D)
    (hd0 : D ≤ 4 * d0) (hd1 : D ≤ 4 * d1)
    (hbit : 0 ≤ bitCost)
    (hcount : costs.length ≤
      rawSymbolicWork Q operations p D d0 d1 (denseArithmeticEvents D))
    (hevent : ∀ t ∈ costs, (t : ℝ) ≤ bitCost)
    (hpoly : bitCost * (Q * operations * SymbolicCost.symbolicFactor D : ℕ) ≤ P) :
    ∃ time : ℕ, RunsIn machine.step time start finish ∧
      (time : ℝ) ≤ 2 * P * ExponentArithmetic.fieldCost (p : ℝ) (D : ℝ) :=
  symbolic_schedule_has_bounded_run costs execution hp hD hdims hd0 hd1
    (denseArithmeticEvents_le D) hbit hcount hevent hpoly

theorem leaf_total_le {P E W : ℝ} {w : Work}
    (h : WorkBounds P E W w) (hP : 0 ≤ P) (hW : 1 ≤ W)
    {v : LeafWork} (hv : v ∈ w.leaves) :
    (v.total : ℝ) ≤ 6 * P * W := by
  have hpw : P ≤ P * W := le_mul_of_one_le_right hP hW
  have h₁ := h.tables v hv
  have h₂ := h.layout v hv
  have h₃ := h.inner v hv
  have h₄ := h.interpolation v hv
  have h₅ := h.output v hv
  simp only [LeafWork.total, LeafWork.schedule, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.cast_add]
  nlinarith

/-- Complete numerical assembly, charging all node work and all five leaf
phases.  The square of the common polynomial pays for the node count and
per-node/per-leaf work; the harmless coefficient eight includes initialization. -/
theorem total_le_eight_polynomial_sq {P E W : ℝ} {w : Work}
    (h : WorkBounds P E W w) (hP : 1 ≤ P) (hE : 1 ≤ E) (hW : 1 ≤ W) :
    (w.total : ℝ) ≤ 8 * P ^ 2 * E * W := by
  have hP0 : 0 ≤ P := le_trans (by norm_num) hP
  have hW0 : 0 ≤ W := le_trans (by norm_num) hW
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have htree : (w.tree.sum : ℝ) ≤ (w.tree.length : ℝ) * P := by
    simpa using sum_cast_le_length_mul w.tree id P h.node_work
  have hleaf := sum_cast_le_length_mul w.leaves LeafWork.total (6 * P * W)
    (fun v hv => leaf_total_le h hP0 hW hv)
  have hcount : (w.leaves.length : ℝ) ≤ w.tree.length := by
    exact_mod_cast h.leaf_count
  have hleaf' : ((w.leaves.map LeafWork.total).sum : ℝ) ≤
      (w.tree.length : ℝ) * (6 * P * W) :=
    hleaf.trans (mul_le_mul_of_nonneg_right hcount (by positivity))
  have htree' : (w.tree.sum : ℝ) ≤ (w.tree.length : ℝ) * (P * W) :=
    htree.trans (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_right hP0 hW) (Nat.cast_nonneg _))
  have hbody : (w.total : ℝ) ≤ P + (w.tree.length : ℝ) * (7 * P * W) := by
    simp only [Work.total, Nat.cast_add]
    nlinarith [h.startup]
  have hbody' : (w.total : ℝ) ≤ P + P * E * (7 * P * W) :=
    hbody.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right h.node_count (by positivity)) P)
  have hstart : P ≤ P ^ 2 * E * W := by
    calc
      P ≤ P * P := le_mul_of_one_le_right hP0 hP
      _ ≤ P * P * E := le_mul_of_one_le_right (mul_nonneg hP0 hP0) hE
      _ ≤ P * P * E * W := le_mul_of_one_le_right (by positivity) hW
      _ = P ^ 2 * E * W := by ring
  nlinarith

theorem polynomial_sq (C : ℝ) (d L : ℕ) :
    polynomial C d L ^ 2 = C ^ 2 * ((L : ℝ) + 1) ^ (2 * d) := by
  simp only [polynomial, mul_pow, ← pow_mul, Nat.mul_comm d 2]

/-- An exponential bound can be substituted only after the phase budgets
have been supplied. This remains a numerical theorem about `Work.total`. -/
theorem total_le_runtimeBound {C E W K : ℝ} {d L n : ℕ} {w : Work}
    (h : WorkBounds (polynomial C d L) E W w)
    (hC : 1 ≤ C) (hE : 1 ≤ E) (hW : 1 ≤ W)
    (hEW : E * W ≤ K * (2 : ℝ) ^ ((9 / 10 : ℝ) * (n : ℝ))) :
    (w.total : ℝ) ≤ runtimeBound (8 * C ^ 2 * K) (2 * d) (9 / 10) L n := by
  have hpoly := one_le_polynomial hC d L
  calc
    (w.total : ℝ) ≤ 8 * polynomial C d L ^ 2 * E * W :=
      total_le_eight_polynomial_sq h hpoly hE hW
    _ = 8 * polynomial C d L ^ 2 * (E * W) := by ring
    _ ≤ 8 * polynomial C d L ^ 2 *
        (K * (2 : ℝ) ^ ((9 / 10 : ℝ) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hEW (by positivity)
    _ = runtimeBound (8 * C ^ 2 * K) (2 * d) (9 / 10) L n := by
      rw [polynomial_sq]
      unfold runtimeBound
      rw [Real.rpow_eq_pow]
      ring

theorem large_input_bound {C p : ℝ} {d L n ell D : ℕ} {w : Work}
    (h : WorkBounds (polynomial C d L) (treeExponential n)
      (ExponentArithmetic.fieldCost p (D : ℝ)) w)
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hell : 4096 ≤ ell)
    (hD : (D : ℝ) ≤ (n : ℝ) / (ell : ℝ) + 1)
    (hlog : ExponentArithmetic.log2 p ≤ (ell : ℝ) + 1) :
    (w.total : ℝ) ≤ runtimeBound
      (8 * C ^ 2 * ExponentArithmetic.fixedFactor p) (2 * d) (9 / 10) L n := by
  apply total_le_runtimeBound h hC (one_le_treeExponential n) (one_le_fieldCost hp D)
  exact ExponentArithmetic.combinedCost_le_09 hp (Nat.cast_nonneg _)
    (by exact_mod_cast hell) hD hlog

/-- Includes sparsifying the bounded-variable input before exhaustive leaf
search, as in the manuscript. Thus no unproved early-bypass optimization is
needed for the small-input case. -/
def smallFactor (B : ℕ) : ℝ :=
  (2 : ℝ) ^ ((B : ℝ) / 32) * SmallInputs.bruteForceFactor B

theorem smallFactor_pos (B : ℕ) : 0 < smallFactor B :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (SmallInputs.bruteForceFactor_pos B)

theorem small_combined_bound {n B : ℕ} (hn : n ≤ B) :
    treeExponential n * (2 : ℝ) ^ (n : ℝ) ≤
      smallFactor B * (2 : ℝ) ^ ((9 / 10 : ℝ) * (n : ℝ)) := by
  have hnR : (n : ℝ) ≤ B := by exact_mod_cast hn
  have ht : treeExponential n ≤ (2 : ℝ) ^ ((B : ℝ) / 32) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hb := SmallInputs.bruteForce_le_saved hn
  calc
    treeExponential n * (2 : ℝ) ^ (n : ℝ) ≤
        (2 : ℝ) ^ ((B : ℝ) / 32) *
          (SmallInputs.bruteForceFactor B * SmallInputs.savedExponential n) :=
      mul_le_mul ht hb (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
    _ = smallFactor B * (2 : ℝ) ^ ((9 / 10 : ℝ) * (n : ℝ)) := by
      unfold smallFactor SmallInputs.savedExponential
      ring

theorem small_input_bound {C : ℝ} {d L n B : ℕ} {w : Work}
    (h : WorkBounds (polynomial C d L) (treeExponential n)
      ((2 : ℝ) ^ (n : ℝ)) w) (hC : 1 ≤ C) (hn : n ≤ B) :
    (w.total : ℝ) ≤ runtimeBound
      (8 * C ^ 2 * smallFactor B) (2 * d) (9 / 10) L n := by
  apply total_le_runtimeBound h hC (one_le_treeExponential n)
    (Real.one_le_rpow (by norm_num) (Nat.cast_nonneg _))
  exact small_combined_bound hn

theorem runtimeBound_mono_constant {C C' s : ℝ} (d L n : ℕ) (hC : C ≤ C') :
    runtimeBound C d s L n ≤ runtimeBound C' d s L n := by
  unfold runtimeBound
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (by positivity)) (Real.rpow_nonneg (by norm_num) _)

/-- Open implementation certificates, with all phase bounds visible.

For every encoded input, an inhabitant must provide (1) traces of the same
primitive machine, (2) a correct output, (3) bounded all-node enumeration,
(4) polynomial node and initialization work, (5) table construction,
(6) layout construction, (7) symbolic arithmetic or exhaustive-search bit
cost, (8) CRT reconstruction, and (9) the final output cost.

In particular this record is not discharged by operation-count/cardinality
theorems, by an abstract cost annotation, or by a semantic SAT function. -/
structure ImplementationCertificates (machine : PrimitiveMachine) (width : ℕ)
    (C : ℝ) (d : ℕ) (p : ℝ) (ell Dstar : ℕ) : Prop where
  large : ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    Dstar ≤ SmallInputs.packedDimension n ell →
    ∃ (answer : Bool) (w : Work),
      Nonempty (PipelineExecution machine F answer w) ∧
      Nonempty (ReductionCertificate F answer w) ∧
      WorkBounds (polynomial C d (Encoding.formulaBitLength F)) (treeExponential n)
        (ExponentArithmetic.fieldCost p (SmallInputs.packedDimension n ell : ℝ)) w
  small : ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    SmallInputs.packedDimension n ell < Dstar →
    ∃ (answer : Bool) (w : Work),
      Nonempty (PipelineExecution machine F answer w) ∧
      Nonempty (ReductionCertificate F answer w) ∧
      WorkBounds (polynomial C d (Encoding.formulaBitLength F)) (treeExponential n)
        ((2 : ℝ) ^ (n : ℝ)) w

/-- The final bridge is conditional on the explicitly listed primitive-machine
certificates. Neither existence of the machine nor these certificates is
asserted by this module. -/
theorem decidesWithBound_of_certificates {machine : PrimitiveMachine}
    {width d ell Dstar : ℕ} {C p : ℝ}
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hell : 4096 ≤ ell)
    (hlog : ExponentArithmetic.log2 p ≤ (ell : ℝ) + 1)
    (cert : ImplementationCertificates machine width C d p ell Dstar) :
    DecidesWithBound machine width
      (8 * C ^ 2 * (ExponentArithmetic.fixedFactor p + smallFactor (ell * Dstar)))
      (2 * d) (9 / 10) := by
  intro n F hF
  have hellpos : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hellpos
  have hC0 : 0 ≤ 8 * C ^ 2 := by positivity
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  by_cases hlarge : Dstar ≤ SmallInputs.packedDimension n ell
  · obtain ⟨answer, w, ⟨execution⟩, ⟨reduction⟩, bounds⟩ := cert.large n F hF hlarge
    refine ⟨answer, w.total, execution.outputs, reduction.correct, ?_⟩
    have htime := large_input_bound bounds hC hp hell
      (ExponentArithmetic.ceil_div_le_add_one (Nat.cast_nonneg n) hellR) hlog
    apply htime.trans
    apply runtimeBound_mono_constant
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (smallFactor_pos (ell * Dstar)).le) hC0
  · have hsmall : SmallInputs.packedDimension n ell < Dstar := Nat.lt_of_not_ge hlarge
    obtain ⟨answer, w, ⟨execution⟩, ⟨reduction⟩, bounds⟩ := cert.small n F hF hsmall
    refine ⟨answer, w.total, execution.outputs, reduction.correct, ?_⟩
    have htime := small_input_bound bounds hC (SmallInputs.variables_le_threshold hellpos hsmall)
    apply htime.trans
    apply runtimeBound_mono_constant
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (ExponentArithmetic.fixedFactor_pos hp0).le) hC0

theorem exponentFeasible_of_certificates {machine : PrimitiveMachine}
    {width d ell Dstar : ℕ} {C p : ℝ}
    (hC : 1 ≤ C) (hd : 0 < d) (hp : 1 ≤ p) (hell : 4096 ≤ ell)
    (hlog : ExponentArithmetic.log2 p ≤ (ell : ℝ) + 1)
    (cert : ImplementationCertificates machine width C d p ell Dstar) :
    ExponentFeasible width (9 / 10 : ℝ) := by
  refine ⟨machine,
    8 * C ^ 2 * (ExponentArithmetic.fixedFactor p + smallFactor (ell * Dstar)),
    2 * d, ?_, by omega, decidesWithBound_of_certificates hC hp hell hlog cert⟩
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have h₁ := ExponentArithmetic.fixedFactor_pos hp0
  have h₂ := smallFactor_pos (ell * Dstar)
  positivity

end

end SubexponentialSAT.RuntimeAssembly

end OAI.Algorithms
