import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CayleyFourier
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

/-! A bipartite regular Cayley multigraph with explicit ordered ports.
Every pair `(x,i)` is a separate edge, including repeated shifts. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators
open SubexponentialSAT.SqrtLog.SparseCode

variable {r : ℕ} {P : Type*}

/-- The involutive port rotation retains the port even for parallel edges. -/
def graph (shifts : P → Cube r) : PortGraph (Cube r) P where
  rotation := {
    toFun := fun e => (e.1 + shifts e.2, e.2)
    invFun := fun e => (e.1 + shifts e.2, e.2)
    left_inv := by rintro ⟨x, i⟩; simp [add_assoc]
    right_inv := by rintro ⟨x, i⟩; simp [add_assoc] }

@[simp] theorem graph_rotation (shifts : P → Cube r) (x : Cube r) (i : P) :
    (graph shifts).rotation (x, i) = (x + shifts i, i) := rfl

@[simp] theorem graph_rotation_symm (shifts : P → Cube r) (x : Cube r) (i : P) :
    (graph shifts).rotation.symm (x, i) = (x + shifts i, i) := rfl

noncomputable def indicator (U : Finset (Cube r)) (x : Cube r) : ℝ :=
  if x ∈ U then 1 else 0

@[simp] theorem sum_indicator (U : Finset (Cube r)) :
    (∑ x, indicator U x) = (U.card : ℝ) := by
  classical
  simp [indicator]

@[simp] theorem sum_indicator_sq (U : Finset (Cube r)) :
    (∑ x, indicator U x ^ 2) = (U.card : ℝ) := by
  classical
  simp [indicator]

variable [Fintype P]

theorem edgeCount_eq_pairing (shifts : P → Cube r) (U W : Finset (Cube r)) :
    ((graph shifts).edgeCount U W : ℝ) =
      ∑ x, indicator U x * adjacency shifts (indicator W) x := by
  classical
  simp only [PortGraph.edgeCount, PortGraph.edgesBetween, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, Fintype.sum_prod_type,
    graph_rotation, indicator, adjacency, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ U <;> by_cases hw : x + shifts i ∈ W <;>
    simp [ hx, hw]

/-- Small nonconstant Walsh sums imply the edge mixing inequality used by
Tanner-code distance. This includes the zero-dimensional cube and empty ports. -/
theorem hasMixing_of_smallWalsh (shifts : P → Cube r) (ε : ℝ)
    (hε : 0 ≤ ε) (hW : SmallWalsh shifts ε) : (graph shifts).HasMixing ε := by
  classical
  intro U W
  have h := adjacency_pairing_le shifts ε hε hW (indicator U) (indicator W)
  rw [← edgeCount_eq_pairing] at h
  simp only [sum_indicator, sum_indicator_sq] at h
  rw [sqrt_scaled_product _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at h
  have hN : (0 : ℝ) < Fintype.card (Cube r) := by
    exact_mod_cast Fintype.card_pos
  apply le_of_mul_le_mul_left ?_ hN
  convert h using 1 ; field_simp

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
