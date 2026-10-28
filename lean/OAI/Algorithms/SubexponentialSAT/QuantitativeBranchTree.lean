import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationBudget
import OAI.Algorithms.SubexponentialSAT.BranchTree
import OAI.Algorithms.SubexponentialSAT.Sparsify

namespace OAI.Algorithms

/-!
# Quantitative binary-tree counting with a variable exponential budget

Appendix A.2 of the subexponential manuscript. All constants remain visible:
M, C, and the exponential budget σ may vary between inputs. The finite encoding
and real-cutoff binomial estimate are imported from the frozen BranchTree module.
-/

namespace SubexponentialSAT.QuantitativeBranchTree

open Finset
open scoped BigOperators

/-- A variable exponential budget, with the complete finite prefactor exposed.
The budget itself suffices; positivity of σ need not be a separate premise. -/
theorem card_paths_le_exponential (P : Finset (List Bool))
    (C k n M : ℕ) (σ : ℝ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.log (4 * (C : ℝ) * M / k) ≤ Real.log 2 * σ)
    (hdepth : ∀ p ∈ P, p.length ≤ C * n)
    (hB : ∀ p ∈ P, (BranchTree.bPositions p).card ≤ k * n / M) :
    (P.card : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) * ((k * n / M + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (σ * n) := by
  by_cases hn : n = 0
  · subst n
    have hcount := BranchTree.card_paths_le P (C * 0) (k * 0 / M) hdepth hB
    have hone : P.card ≤ 1 := by simpa using hcount
    simpa using (show (P.card : ℝ) ≤ 1 by exact_mod_cast hone)
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hMpos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  let q : ℝ := (k : ℝ) * n / M
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : q ≤ (C * n : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hDim hnpos.le
    simpa [q, Nat.cast_mul, div_mul_eq_mul_div] using h
  have hR : ((k * n / M : ℕ) : ℝ) ≤ q := by
    simpa [q, Nat.cast_mul] using (Nat.cast_div_le (m := k * n) (n := M) (α := ℝ))
  have hbase : 4 * ((C * n : ℕ) : ℝ) / q = 4 * (C : ℝ) * M / k := by
    dsimp [q]
    push_cast
    field_simp
  have hb : q * Real.log (4 * ((C * n : ℕ) : ℝ) / q) ≤
      Real.log 2 * (σ * n) := by
    rw [hbase]
    dsimp [q]
    calc
      ((k : ℝ) * n / M) * Real.log (4 * (C : ℝ) * M / k) =
          ((k : ℝ) / M * Real.log (4 * (C : ℝ) * M / k)) * n := by ring
      _ ≤ (Real.log 2 * σ) * n := mul_le_mul_of_nonneg_right hbudget hnpos.le
      _ = Real.log 2 * (σ * n) := by ring
  have h := BranchTree.card_paths_le_two_rpow P (C * n) (k * n / M)
    hq hD hR hdepth hB hb
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Conversion of the manuscript's base-two logarithmic budget. -/
theorem natural_log_budget_of_logb (C k M : ℕ) (σ : ℝ)
    (hbudget : (k : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M / k) ≤ σ) :
    (k : ℝ) / M * Real.log (4 * (C : ℝ) * M / k) ≤ Real.log 2 * σ := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, ← mul_div_assoc, div_le_iff₀ htwo] at hbudget
  simpa [mul_comm] using hbudget

/-- Node-count form for an actual inductive finite tree. -/
theorem nodeCount_le_exponential (t : BranchTree.Tree)
    (C k n M : ℕ) (σ : ℝ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M / k) ≤ σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ k * n / M) :
    (t.nodeCount : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) * ((k * n / M + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (σ * n) := by
  rw [← t.card_paths]
  apply card_paths_le_exponential t.paths C k n M σ hk hM hDim
    (natural_log_budget_of_logb C k M σ hbudget) hdepth
  intro p hp
  rw [BranchTree.card_bPositions_eq_count]
  exact hB p hp

/-- Explicit quadratic dependence on input size, retaining the C and k factors. -/
theorem nodeCount_le_quadratic (t : BranchTree.Tree)
    (C k n M : ℕ) (σ : ℝ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M / k) ≤ σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ k * n / M) :
    (t.nodeCount : ℝ) ≤ ((C + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
      ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  have hcount := nodeCount_le_exponential t C k n M σ hk hM hDim hbudget hdepth hB
  refine hcount.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _))
  exact_mod_cast BranchTree.polynomial_prefactor_bound C k n M

/-- This version accepts an explicit bound on the coefficient, enabling later
substitution of polynomial bounds in M or in the inverse budget. -/
theorem nodeCount_le_coefficient (t : BranchTree.Tree)
    (C k n M : ℕ) (σ A : ℝ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M / k) ≤ σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ k * n / M)
    (hcoeff : ((C + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ A) :
    (t.nodeCount : ℝ) ≤ A * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  exact (nodeCount_le_quadratic t C k n M σ hk hM hDim hbudget hdepth hB).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num) _))

/-- The actual sunflower decomposition has the required path budgets. Only
its externally chosen quantitative parameter inequalities are inputs here. -/
theorem decomposition_nodeCount_le {n k M : ℕ} {F : SAT.CNF (Fin n)}
    (tree : Sparsify.Decomposition (SparsificationConstants.z M) k F)
    (hM : 2 ≤ M) (hk : 0 < k) (σ : ℝ)
    (hF : SunflowerBranch.Antichain F)
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    (tree.shape.nodeCount : ℝ) ≤ ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply nodeCount_le_quadratic tree.shape (SparsificationConstants.C M (k - 1))
    k n M σ hk (by omega) hDim hbudget
  · intro p hp
    exact (tree.path_budgets hM hF p hp).1
  · intro p hp
    exact (tree.path_budgets hM hF p hp).2

/-- The bound applies to the actual deterministic tree for every input formula.
There are no path-budget or antichain assumptions on the caller. -/
theorem treeFor_nodeCount_le {n : ℕ} (M k : ℕ) (hM : 2 ≤ M) (hk : 0 < k)
    (σ : ℝ) (F : SAT.CNF (Fin n))
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply decomposition_nodeCount_le _ hM hk σ _ hDim hbudget
  exact SunflowerBranch.antichain_absorb _

end SubexponentialSAT.QuantitativeBranchTree

namespace SubexponentialSAT.QuantitativeBranchTree

/-- Explicit polynomial control of the node-count coefficient from C ≤ a*M^b. -/
theorem coefficient_le_polynomial {C M a b : ℕ} (k : ℕ) (hC : C ≤ a * M ^ b) :
    (C + 1) * (k + 1) ≤ (a + 1) * (k + 1) * (M + 1) ^ b := by
  have hpow : M ^ b ≤ (M + 1) ^ b := Nat.pow_le_pow_left (Nat.le_succ M) b
  have hone : 1 ≤ (M + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have hC' : C + 1 ≤ (a + 1) * (M + 1) ^ b := by
    calc
      C + 1 ≤ a * M ^ b + 1 := Nat.add_le_add_right hC 1
      _ ≤ a * (M + 1) ^ b + (M + 1) ^ b :=
        Nat.add_le_add (Nat.mul_le_mul_left a hpow) hone
      _ = (a + 1) * (M + 1) ^ b := by ring
  calc
    (C + 1) * (k + 1) ≤ ((a + 1) * (M + 1) ^ b) * (k + 1) :=
      Nat.mul_le_mul_right _ hC'
    _ = (a + 1) * (k + 1) * (M + 1) ^ b := by ring

/-- The polynomial's coefficient and degree depend only on k; M remains quantified. -/
theorem exists_coefficient_polynomial (k : ℕ) :
    ∃ A d : ℕ, ∀ M, 2 ≤ M →
      (SparsificationConstants.C M (k - 1) + 1) * (k + 1) ≤ A * (M + 1) ^ d := by
  obtain ⟨a, b, hC⟩ := SparsificationConstants.C_polynomialBound (k - 1)
  exact ⟨(a + 1) * (k + 1), b,
    fun M hM => coefficient_le_polynomial k (hC M hM)⟩

/-- Substituting a parameter bound M ≤ A*X^d does not conceal any dependence on X. -/
theorem coefficient_le_of_parameter_bound {C M a b : ℕ} (k : ℕ)
    (X A : ℝ) (d : ℕ) (hC : C ≤ a * M ^ b) (hX : 1 ≤ X)
    (hM : (M : ℝ) ≤ A * X ^ d) :
    ((C + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
      ((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (A + 1) ^ b * X ^ (d * b) := by
  have hXp : 1 ≤ X ^ d := one_le_pow₀ hX
  have hMp : (M : ℝ) + 1 ≤ (A + 1) * X ^ d := by nlinarith
  have hleft : 0 ≤ (M : ℝ) + 1 := by positivity
  have hp : ((M : ℝ) + 1) ^ b ≤ ((A + 1) * X ^ d) ^ b :=
    pow_le_pow_left₀ hleft hMp b
  have hc : ((C + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
      ((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * ((M : ℝ) + 1) ^ b := by
    exact_mod_cast coefficient_le_polynomial k hC
  calc
    ((C + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
        ((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * ((M : ℝ) + 1) ^ b := hc
    _ ≤ ((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * ((A + 1) * X ^ d) ^ b :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (A + 1) ^ b * X ^ (d * b) := by
      rw [mul_pow, ← pow_mul]
      ring

/-- A complete node estimate exposing both the parameter polynomial and the
variable exponential rate. X can later be instantiated as 1/σ+2. -/
theorem nodeCount_le_parameter_bound (t : BranchTree.Tree)
    (C k n M a b d : ℕ) (σ X A : ℝ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.logb 2 (4 * (C : ℝ) * M / k) ≤ σ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ k * n / M)
    (hC : C ≤ a * M ^ b) (hX : 1 ≤ X) (hparam : (M : ℝ) ≤ A * X ^ d) :
    (t.nodeCount : ℝ) ≤
      (((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (A + 1) ^ b) *
      X ^ (d * b) * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply nodeCount_le_coefficient t C k n M σ _ hk hM hDim hbudget hdepth hB
  exact coefficient_le_of_parameter_bound k X A d hC hX hparam

end SubexponentialSAT.QuantitativeBranchTree

namespace SubexponentialSAT.QuantitativeBranchTree

/-- The parameter-polynomial estimate for the tree computed from a formula. -/
theorem treeFor_nodeCount_le_parameter_bound {n : ℕ} (M k a b d : ℕ)
    (hM : 2 ≤ M) (hk : 0 < k) (σ X A : ℝ) (F : SAT.CNF (Fin n))
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ)
    (hC : SparsificationConstants.C M (k - 1) ≤ a * M ^ b)
    (hX : 1 ≤ X) (hparam : (M : ℝ) ≤ A * X ^ d) :
    ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
      (((a + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (A + 1) ^ b) *
      X ^ (d * b) * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  apply nodeCount_le_parameter_bound _ (SparsificationConstants.C M (k - 1))
    k n M a b d σ X A hk (by omega) hDim hbudget
  · intro p hp
    exact ((Sparsify.treeFor M k hM F).path_budgets hM
      (SunflowerBranch.antichain_absorb _) p hp).1
  · intro p hp
    exact ((Sparsify.treeFor M k hM F).path_budgets hM
      (SunflowerBranch.antichain_absorb _) p hp).2
  · exact hC
  · exact hX
  · exact hparam

/-- The coefficient and degree are fixed before M, σ, n, and F vary. -/
theorem exists_treeFor_node_polynomial_M (k : ℕ) (hk : 0 < k) :
    ∃ A d : ℕ, ∀ (M : ℕ) (hM : 2 ≤ M) (σ : ℝ),
      (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1) →
      (k : ℝ) / M *
        Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ →
      ∀ {n : ℕ} (F : SAT.CNF (Fin n)),
        ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
          (A : ℝ) * ((M : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  obtain ⟨A, d, hcoeff⟩ := exists_coefficient_polynomial k
  refine ⟨A, d, ?_⟩
  intro M hM σ hDim hbudget n F
  have hc : ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) ≤ (A : ℝ) * ((M : ℝ) + 1) ^ d := by
    exact_mod_cast hcoeff M hM
  exact (treeFor_nodeCount_le M k hM hk σ F hDim hbudget).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num) _))

/-- The explicitly returned family is no larger than the tree that computes it. -/
theorem treeFor_leaves_length_le {n : ℕ} (M k : ℕ) (hM : 2 ≤ M) (hk : 0 < k)
    (σ : ℝ) (F : SAT.CNF (Fin n))
    (hDim : (k : ℝ) / M ≤ SparsificationConstants.C M (k - 1))
    (hbudget : (k : ℝ) / M *
      Real.logb 2 (4 * (SparsificationConstants.C M (k - 1) : ℝ) * M / k) ≤ σ) :
    ((Sparsify.treeFor M k hM F).leaves.length : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (σ * n) := by
  refine le_trans ?_ (treeFor_nodeCount_le M k hM hk σ F hDim hbudget)
  exact_mod_cast (Sparsify.treeFor M k hM F).leaves_length_le_nodes

end SubexponentialSAT.QuantitativeBranchTree

namespace SubexponentialSAT.QuantitativeBranchTree

/-- The reciprocal-budget selector discharges all numerical budget assumptions
for the actual formula-dependent tree. -/
theorem selected_nodeCount_le {n : ℕ} (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (hs : 0 < s)
    (F : SAT.CNF (Fin n)) :
    let M := SparsificationBudget.chooseM k hk s
    let hM := SparsificationBudget.chooseM_ge_two k hk s
    ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
      ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s) := by
  dsimp
  have hspec := SparsificationBudget.chooseM_spec k hk s hs
  have h := treeFor_nodeCount_le (SparsificationBudget.chooseM k hk s) k
    (SparsificationBudget.chooseM_ge_two k hk s) (by omega) ((1 : ℝ) / s) F
    hspec.ratio_le (hspec.logb_budget hk hs)
  simpa only [one_div, inv_mul_eq_div] using h

/-- A single polynomial works for every inverse budget s and every input.
The existential constants are quantified before s, n, and F. -/
theorem exists_selected_node_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A d : ℕ, ∀ (s : ℕ) (_hs : 0 < s) {n : ℕ} (F : SAT.CNF (Fin n)),
      let M := SparsificationBudget.chooseM k hk s
      let hM := SparsificationBudget.chooseM_ge_two k hk s
      ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
        (A : ℝ) * (s : ℝ) ^ d * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s) := by
  obtain ⟨a, b, hC⟩ := SparsificationConstants.C_polynomialBound (k - 1)
  obtain ⟨K, T, hK⟩ := SparsificationBudget.chooseM_quadratic_bound k hk
  refine ⟨(a + 1) * (k + 1) * (K + 1) ^ b, 2 * b, ?_⟩
  intro s hs n F
  dsimp
  let M := SparsificationBudget.chooseM k hk s
  have hM : 2 ≤ M := SparsificationBudget.chooseM_ge_two k hk s
  have hspec : SparsificationBudget.ReciprocalAdmissible k s M :=
    SparsificationBudget.chooseM_spec k hk s hs
  have hX : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hparam : (M : ℝ) ≤ (K : ℝ) * (s : ℝ) ^ 2 := by
    exact_mod_cast (hK s hs).1
  have h := treeFor_nodeCount_le_parameter_bound M k a b 2 hM (by omega)
    ((1 : ℝ) / s) (s : ℝ) (K : ℝ) F hspec.ratio_le (hspec.logb_budget hk hs)
    (hC M hM) hX hparam
  simpa only [M, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
    one_div, inv_mul_eq_div] using h

/-- The explicit returned family obeys the same uniformly quantified polynomial. -/
theorem exists_selected_leaves_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A d : ℕ, ∀ (s : ℕ) (_hs : 0 < s) {n : ℕ} (F : SAT.CNF (Fin n)),
      let M := SparsificationBudget.chooseM k hk s
      let hM := SparsificationBudget.chooseM_ge_two k hk s
      ((Sparsify.treeFor M k hM F).leaves.length : ℝ) ≤
        (A : ℝ) * (s : ℝ) ^ d * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s) := by
  obtain ⟨A, d, hbound⟩ := exists_selected_node_polynomial k hk
  refine ⟨A, d, ?_⟩
  intro s hs n F
  refine le_trans ?_ (hbound s hs F)
  exact_mod_cast (Sparsify.treeFor (SparsificationBudget.chooseM k hk s) k
    (SparsificationBudget.chooseM_ge_two k hk s) F).leaves_length_le_nodes

end SubexponentialSAT.QuantitativeBranchTree

namespace SubexponentialSAT.QuantitativeBranchTree

/-- Rational budget lift. The coefficient A and degree d depend only on k, and
are fixed before numerator a, denominator b, input size n, and formula F vary. -/
theorem exists_rational_selected_node_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A d : ℕ, ∀ (a b : ℕ), 0 < a → a ≤ b →
      ∀ {n : ℕ} (F : SAT.CNF (Fin n)),
        let M := SparsificationBudget.chooseRationalM k hk a b
        let hM := SparsificationBudget.chooseM_ge_two k hk
          (SparsificationBudget.reciprocalIndex a b)
        ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
          (A : ℝ) * ((b : ℝ) / a + 2) ^ d * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ (((a : ℝ) / b) * n) := by
  obtain ⟨A, d, hbound⟩ := exists_selected_node_polynomial k hk
  refine ⟨A, d, ?_⟩
  intro a b ha hab n F
  let s := SparsificationBudget.reciprocalIndex a b
  have hs : 0 < s := by have := SparsificationBudget.reciprocalIndex_ge_two a b; dsimp [s]; omega
  have h := hbound s hs F
  have hidx : (s : ℝ) ≤ (b : ℝ) / a + 2 :=
    SparsificationBudget.reciprocalIndex_le_inverse_add_two a b ha
  have hp : (s : ℝ) ^ d ≤ ((b : ℝ) / a + 2) ^ d :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hidx d
  have hpoly : (A : ℝ) * (s : ℝ) ^ d * ((n : ℝ) + 1) ^ 2 ≤
      (A : ℝ) * ((b : ℝ) / a + 2) ^ d * ((n : ℝ) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
      (sq_nonneg _)
  have he : (2 : ℝ) ^ ((n : ℝ) / s) ≤ (2 : ℝ) ^ (((a : ℝ) / b) * n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hx := mul_le_mul_of_nonneg_right
      (SparsificationBudget.reciprocalIndex_budget a b ha hab) (Nat.cast_nonneg n)
    simpa only [s, one_div, inv_mul_eq_div] using hx
  exact h.trans (mul_le_mul hpoly he (Real.rpow_nonneg (by norm_num) _) (by positivity))

/-- The actual output family has the same rational-budget size bound. -/
theorem exists_rational_selected_leaves_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A d : ℕ, ∀ (a b : ℕ), 0 < a → a ≤ b →
      ∀ {n : ℕ} (F : SAT.CNF (Fin n)),
        let M := SparsificationBudget.chooseRationalM k hk a b
        let hM := SparsificationBudget.chooseM_ge_two k hk
          (SparsificationBudget.reciprocalIndex a b)
        ((Sparsify.treeFor M k hM F).leaves.length : ℝ) ≤
          (A : ℝ) * ((b : ℝ) / a + 2) ^ d * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ (((a : ℝ) / b) * n) := by
  obtain ⟨A, d, hbound⟩ := exists_rational_selected_node_polynomial k hk
  refine ⟨A, d, ?_⟩
  intro a b ha hab n F
  refine le_trans ?_ (hbound a b ha hab F)
  exact_mod_cast (Sparsify.treeFor (SparsificationBudget.chooseRationalM k hk a b) k
    (SparsificationBudget.chooseM_ge_two k hk (SparsificationBudget.reciprocalIndex a b))
      F).leaves_length_le_nodes

end SubexponentialSAT.QuantitativeBranchTree

namespace SubexponentialSAT.QuantitativeBranchTree

/-- Direct rational-budget statement of the node bound in Lemma 2.1.
All selected parameters are concrete and the polynomial is uniform in σ and n. -/
theorem exists_sigma_selected_node_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A d : ℕ, ∀ (σ : ℚ), 0 < σ → σ ≤ 1 →
      ∀ {n : ℕ} (F : SAT.CNF (Fin n)),
        let M := SparsificationBudget.chooseForSigma k hk σ
        let hM := SparsificationBudget.chooseForSigma_ge_two k hk σ
        ((Sparsify.treeFor M k hM F).shape.nodeCount : ℝ) ≤
          (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ d * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨A, d, hbound⟩ := exists_rational_selected_node_polynomial k hk
  refine ⟨A, d, ?_⟩
  intro σ hσ hσone n F
  have hdata := SparsificationBudget.rational_num_data σ hσ
  have h := hbound σ.num.natAbs σ.den hdata.1
    (SparsificationBudget.rational_num_le_den σ hσ hσone) F
  have hinv : (σ.den : ℝ) / σ.num.natAbs = (σ : ℝ)⁻¹ := by
    rw [← hdata.2, inv_div]
  simpa only [SparsificationBudget.chooseForSigma, hdata.2, hinv] using h

/-- Direct rational-budget bound for the explicit returned leaf list. -/
theorem exists_sigma_selected_leaves_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A d : ℕ, ∀ (σ : ℚ), 0 < σ → σ ≤ 1 →
      ∀ {n : ℕ} (F : SAT.CNF (Fin n)),
        let M := SparsificationBudget.chooseForSigma k hk σ
        let hM := SparsificationBudget.chooseForSigma_ge_two k hk σ
        ((Sparsify.treeFor M k hM F).leaves.length : ℝ) ≤
          (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ d * ((n : ℝ) + 1) ^ 2 *
            (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨A, d, hbound⟩ := exists_sigma_selected_node_polynomial k hk
  refine ⟨A, d, ?_⟩
  intro σ hσ hσone n F
  refine le_trans ?_ (hbound σ hσ hσone F)
  exact_mod_cast (Sparsify.treeFor (SparsificationBudget.chooseForSigma k hk σ) k
    (SparsificationBudget.chooseForSigma_ge_two k hk σ) F).leaves_length_le_nodes

end SubexponentialSAT.QuantitativeBranchTree

end OAI.Algorithms
