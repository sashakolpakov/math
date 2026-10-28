import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutParameters

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

structure Input where
  ambient : ℕ
  freeCount : ℕ
  clauses : ℕ
  width : ℕ
  factors : ℕ
  occurrence : ℕ
  arity : ℕ
  incidences : ℕ
  deriving DecidableEq, Repr

structure Parameters where
  L : ℕ
  w : ℕ
  s : ℕ
  r : ℕ
  Q : ℕ
  R : ℕ
  epsilonDen : ℕ
  t : ℕ
  d : ℕ
  N : ℕ
  J : ℕ
  deriving DecidableEq, Repr

def precision (ambient clauses : ℕ) : ℕ := ambient + Nat.size clauses + 1

def extensionDegree (Q : ℕ) : ℕ := Nat.size Q + 1

def produce (x : Input) : Parameters :=
  let n := x.freeCount
  let r := Asymptotic.layoutR n
  let Q := Asymptotic.layoutQ n
  let R := Asymptotic.layoutCutoff n x.occurrence
  let t := precision x.ambient x.clauses
  { L := Asymptotic.L n
    w := Asymptotic.w n
    s := Asymptotic.s n
    r := r
    Q := Q
    R := R
    epsilonDen := 32 * x.occurrence * r * Asymptotic.L n ^ 2
    t := t
    d := extensionDegree Q
    N := r ^ (2 * Q)
    J := x.width * R * (2 * x.factors + 3 * (t - 1) + 1) / Q + 1 }

theorem precision_pos (n m : ℕ) : 0 < precision n m := by
  unfold precision
  omega

theorem extensionDegree_pos (Q : ℕ) : 0 < extensionDegree Q := by
  unfold extensionDegree
  omega

theorem precision_sufficient (n m : ℕ) : m * 2 ^ n < 3 ^ precision n m := by
  have hm := Nat.lt_size_self m
  have hp : 0 < 2 ^ n := Nat.pow_pos (by decide)
  calc
    m * 2 ^ n < 2 ^ Nat.size m * 2 ^ n := Nat.mul_lt_mul_of_pos_right hm hp
    _ = 2 ^ (n + Nat.size m) := by rw [pow_add]; ring
    _ ≤ 3 ^ (n + Nat.size m) := Nat.pow_le_pow_left (by decide) _
    _ < 3 ^ precision n m := by
      unfold precision
      exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem extensionDegree_sufficient (Q : ℕ) : Q < 3 ^ extensionDegree Q := by
  calc
    Q < 2 ^ Nat.size Q := Nat.lt_size_self Q
    _ ≤ 3 ^ Nat.size Q := Nat.pow_le_pow_left (by decide) _
    _ ≤ 3 ^ extensionDegree Q := Nat.pow_le_pow_right (by decide) (by unfold extensionDegree; omega)

theorem produce_r_ge_two (x : Input) : 2 ≤ (produce x).r := Asymptotic.layoutR_ge_two _
theorem produce_R_ge_four (x : Input) : 4 ≤ (produce x).R := Asymptotic.layoutCutoff_ge_four _ _
theorem produce_t_pos (x : Input) : 0 < (produce x).t := precision_pos _ _
theorem produce_d_pos (x : Input) : 0 < (produce x).d := extensionDegree_pos _
theorem produce_J_pos (x : Input) : 0 < (produce x).J := Nat.succ_pos _

theorem produce_epsilonDen_pos (x : Input) (hb : 0 < x.occurrence) :
    0 < (produce x).epsilonDen := by
  have hr := Asymptotic.layoutR_ge_two x.freeCount
  have hL := Asymptotic.L_pos x.freeCount
  dsimp [produce]
  positivity

/-- All runtime guards are integer comparisons. Spectral feasibility follows
from the proved schedule and is never tested by a real-number oracle. -/
def Guard (x : Input) : Prop :=
  0 < x.freeCount ∧ x.freeCount ≤ x.ambient ∧ 0 < x.clauses ∧
  0 < x.occurrence ∧ 0 < x.arity ∧ x.freeCount ≤ x.incidences ∧
  2 ≤ (produce x).Q ∧ 4 * (produce x).R ≤ (produce x).Q ∧
  4 * (x.occurrence + x.arity) * (produce x).N ^ 2 *
      (produce x).epsilonDen ^ 2 ≤ x.incidences ∧
  16 * (produce x).Q * (produce x).r ^ 2 ≤ x.freeCount

instance (x : Input) : Decidable (Guard x) := by unfold Guard; infer_instance

def passes (x : Input) : Bool := decide (Guard x)

@[simp] theorem passes_eq_true (x : Input) : passes x = true ↔ Guard x := by
  simp [passes]

inductive Dispatch where
  | sparse
  | exhaustive
  deriving DecidableEq, Repr

def dispatch (x : Input) : Dispatch := if passes x then .sparse else .exhaustive

@[simp] theorem dispatch_sparse_iff (x : Input) : dispatch x = .sparse ↔ Guard x := by
  simp [dispatch, passes]

@[simp] theorem dispatch_exhaustive_iff (x : Input) : dispatch x = .exhaustive ↔ ¬ Guard x := by
  simp [dispatch, passes]

theorem guard_spectral (x : Input) (h : Guard x) :
    32 * (((produce x).Q - 1 : ℕ) : ℝ) *
      Real.log (2 / (Asymptotic.layoutEpsilon x.freeCount x.occurrence : ℝ)) ≤
        ((produce x).R : ℝ) ^ 2 :=
  Asymptotic.layout_spectral_square _ h.2.2.2.1

/-- Division plus one gives strictly more Hermite conditions than the degree. -/
theorem guard_hermite (x : Input) (h : Guard x) :
    x.width * (produce x).R * (2 * x.factors + 3 * ((produce x).t - 1) + 1) <
      (produce x).Q * (produce x).J := by
  have hq : 0 < (produce x).Q := by have := h.2.2.2.2.2.2.1; omega
  exact Nat.lt_mul_div_succ _ hq

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
