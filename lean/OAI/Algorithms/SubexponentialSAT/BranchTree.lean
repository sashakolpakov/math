import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SparsificationConstants

namespace OAI.Algorithms

/-!
# Counting binary branch-tree paths

False labels an A edge and true labels a B edge. A word is encoded injectively
by its length and the finite set of positions occupied by B. This proves the
finite counting step in Appendix A.3 without any analytic hypotheses.
-/

namespace SubexponentialSAT.BranchTree

open Finset
open scoped BigOperators

/-- The zero-based positions of B edges in an actual binary path. -/
def bPositions (p : List Bool) : Finset ℕ :=
  (range p.length).filter fun i => p[i]? = some true

@[simp] theorem mem_bPositions (p : List Bool) (i : ℕ) :
    i ∈ bPositions p ↔ i < p.length ∧ p[i]? = some true := by
  simp [bPositions]

/-- The B-position set is contained in the range of the path length. -/
theorem bPositions_subset (p : List Bool) : bPositions p ⊆ range p.length :=
  filter_subset _ _

/-- Depth and B positions determine every edge of a binary path. -/
theorem eq_of_length_bPositions_eq {p q : List Bool}
    (hlen : p.length = q.length) (hpos : bPositions p = bPositions q) : p = q := by
  apply List.ext_getElem hlen
  intro i hp hq
  have he : (p[i]'hp = true) ↔ (q[i]'hq = true) := by
    have hm : i ∈ bPositions p ↔ i ∈ bPositions q := by rw [hpos]
    simpa [mem_bPositions, hp, hq, List.getElem?_eq_getElem] using hm
  cases hvp : p[i]'hp <;> cases hvq : q[i]'hq <;> simp_all

/-- The concrete code used in the manuscript. -/
def pathCode (p : List Bool) : ℕ × Finset ℕ := (p.length, bPositions p)

theorem pathCode_injective : Function.Injective pathCode := by
  intro p q h
  exact eq_of_length_bPositions_eq (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- All possible B-position sets of size at most R in a D-position ambient set. -/
def positionSets (D R : ℕ) : Finset (Finset ℕ) :=
  (range (R + 1)).biUnion fun r => (range D).powersetCard r

theorem mem_positionSets {D R : ℕ} {s : Finset ℕ} :
    s ∈ positionSets D R ↔ s ⊆ range D ∧ s.card ≤ R := by
  simp only [positionSets, mem_biUnion, mem_range, mem_powersetCard]
  constructor
  · rintro ⟨r, hr, hs, he⟩
    exact ⟨hs, he ▸ Nat.le_of_lt_succ hr⟩
  · rintro ⟨hs, hc⟩
    exact ⟨s.card, Nat.lt_succ_of_le hc, hs, rfl⟩

theorem card_positionSets_le (D R : ℕ) :
    (positionSets D R).card ≤ ∑ r ∈ range (R + 1), D.choose r := by
  calc
    (positionSets D R).card ≤
        ∑ r ∈ range (R + 1), ((range D).powersetCard r).card := card_biUnion_le
    _ = ∑ r ∈ range (R + 1), D.choose r := by simp

/-- Every finite collection of actual binary paths obeys the node-count bound.
Prefix closure is unnecessary for this stronger statement. -/
theorem card_paths_le (P : Finset (List Bool)) (D R : ℕ)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R) :
    P.card ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r := by
  have hsub : P.image pathCode ⊆ range (D + 1) ×ˢ positionSets D R := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hc
    apply mem_product.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le (hdepth p hp)), ?_⟩
    apply mem_positionSets.mpr
    refine ⟨?_, hB p hp⟩
    exact (bPositions_subset p).trans (range_mono (hdepth p hp))
  calc
    P.card = (P.image pathCode).card := (card_image_of_injective P pathCode_injective).symm
    _ ≤ (range (D + 1) ×ˢ positionSets D R).card := card_le_card hsub
    _ = (D + 1) * (positionSets D R).card := by simp
    _ ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r :=
      Nat.mul_le_mul_left _ (card_positionSets_le D R)

/-- A finite rooted binary tree, with A as its left edge and B as its right edge. -/
inductive Tree where
  | leaf : Tree
  | branch : Tree → Tree → Tree

/-- All root-to-node paths, including the empty path to the root. -/
def Tree.paths : Tree → Finset (List Bool)
  | .leaf => {[]}
  | .branch A B => insert []
      ((A.paths.image (List.cons false)) ∪ (B.paths.image (List.cons true)))

/-- The number of actual nodes of this finite tree. -/
def Tree.nodeCount : Tree → ℕ
  | .leaf => 1
  | .branch A B => 1 + A.nodeCount + B.nodeCount

@[simp] theorem Tree.card_paths (t : Tree) : t.paths.card = t.nodeCount := by
  induction t with
  | leaf => simp [Tree.paths, Tree.nodeCount]
  | branch A B ihA ihB =>
    have hd : Disjoint (A.paths.image (List.cons false))
        (B.paths.image (List.cons true)) := by
      apply disjoint_left.mpr
      intro p hpA hpB
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hpA
      obtain ⟨b, hb, he⟩ := mem_image.mp hpB
      cases he
    have hAinj : Function.Injective (List.cons false : List Bool → List Bool) := by
      intro a b h
      exact List.cons.inj h |>.2
    have hBinj : Function.Injective (List.cons true : List Bool → List Bool) := by
      intro a b h
      exact List.cons.inj h |>.2
    simp only [Tree.paths, Tree.nodeCount]
    rw [Finset.card_insert_of_notMem (by simp), card_union_of_disjoint hd,
      card_image_of_injective _ hAinj, card_image_of_injective _ hBinj, ihA, ihB]
    omega

/-- Appendix A.3's finite-tree bound, with every internal node included. -/
theorem Tree.nodeCount_le (t : Tree) (D R : ℕ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ D)
    (hB : ∀ p ∈ t.paths, (bPositions p).card ≤ R) :
    t.nodeCount ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r := by
  rw [← t.card_paths]
  exact card_paths_le t.paths D R hdepth hB

/-- The paper's exact floor convention: natural division is floor division. -/
theorem Tree.nodeCount_le_sparsification (t : Tree) (C k n M : ℕ)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, (bPositions p).card ≤ k * n / M) :
    t.nodeCount ≤ (C * n + 1) * ∑ r ∈ range (k * n / M + 1), (C * n).choose r :=
  t.nodeCount_le (C * n) (k * n / M) hdepth hB

/-- Any pointwise binomial estimate produces precisely this polynomial factor. -/
theorem card_paths_le_of_choose_le (P : Finset (List Bool)) (D R E : ℕ)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R)
    (hchoose : ∀ r ≤ R, D.choose r ≤ E) :
    P.card ≤ (D + 1) * (R + 1) * E := by
  calc
    P.card ≤ (D + 1) * ∑ r ∈ range (R + 1), D.choose r := card_paths_le P D R hdepth hB
    _ ≤ (D + 1) * ∑ _r ∈ range (R + 1), E := by
      apply Nat.mul_le_mul_left
      exact sum_le_sum fun r hr => hchoose r (Nat.le_of_lt_succ (mem_range.mp hr))
    _ = (D + 1) * (R + 1) * E := by simp [Nat.mul_assoc]

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree

/-- A uniform binomial estimate valid at a real, not necessarily integral, cutoff. -/
theorem choose_le_rpow_real (D r : ℕ) {q : ℝ} (hq : 0 < q)
    (hD : q ≤ D) (hr : (r : ℝ) ≤ q) :
    (D.choose r : ℝ) ≤ (4 * (D : ℝ) / q) ^ q := by
  have hbase : 1 ≤ (D : ℝ) / q := (le_div_iff₀ hq).2 (by simpa using hD)
  have hbasenonneg : 0 ≤ (D : ℝ) / q := le_trans zero_le_one hbase
  have hsplit : (D : ℝ) ^ r / (r.factorial : ℝ) =
      ((D : ℝ) / q) ^ r * (q ^ r / (r.factorial : ℝ)) := by
    rw [div_pow]
    field_simp
  have hpow : ((D : ℝ) / q) ^ r ≤ ((D : ℝ) / q) ^ q := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hbase hr)
  have hexp : Real.exp q ≤ (4 : ℝ) ^ q := by
    rw [← Real.exp_one_rpow]
    exact Real.rpow_le_rpow (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) hq.le
  calc
    (D.choose r : ℝ) ≤ (D : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r D
    _ = ((D : ℝ) / q) ^ r * (q ^ r / (r.factorial : ℝ)) := hsplit
    _ ≤ ((D : ℝ) / q) ^ r * Real.exp q :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp q hq.le r)
        (pow_nonneg hbasenonneg r)
    _ ≤ ((D : ℝ) / q) ^ q * Real.exp q :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg q)
    _ ≤ ((D : ℝ) / q) ^ q * (4 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hbasenonneg _)
    _ = (4 * (D : ℝ) / q) ^ q := by
      rw [← Real.mul_rpow hbasenonneg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree
open Finset
open scoped BigOperators

/-- The finite path bound with an arbitrary positive real cutoff. -/
theorem card_paths_le_rpow_real (P : Finset (List Bool)) (D R : ℕ) {q : ℝ}
    (hq : 0 < q) (hD : q ≤ D) (hR : (R : ℝ) ≤ q)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R) :
    (P.card : ℝ) ≤ ((D : ℝ) + 1) * ((R : ℝ) + 1) * (4 * (D : ℝ) / q) ^ q := by
  have hcount : (P.card : ℝ) ≤ ((D : ℝ) + 1) *
      ∑ r ∈ range (R + 1), (D.choose r : ℝ) := by
    exact_mod_cast card_paths_le P D R hdepth hB
  calc
    (P.card : ℝ) ≤ ((D : ℝ) + 1) *
        ∑ r ∈ range (R + 1), (D.choose r : ℝ) := hcount
    _ ≤ ((D : ℝ) + 1) * ∑ _r ∈ range (R + 1), (4 * (D : ℝ) / q) ^ q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro r hr
      apply choose_le_rpow_real D r hq hD
      exact (Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp hr))).trans hR
    _ = ((D : ℝ) + 1) * ((R : ℝ) + 1) * (4 * (D : ℝ) / q) ^ q := by
      simp [mul_assoc]

/-- The only budget used here is the explicit logarithmic exponent inequality. -/
theorem card_paths_le_two_rpow (P : Finset (List Bool)) (D R : ℕ) {q e : ℝ}
    (hq : 0 < q) (hD : q ≤ D) (hR : (R : ℝ) ≤ q)
    (hdepth : ∀ p ∈ P, p.length ≤ D)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ R)
    (hbudget : q * Real.log (4 * (D : ℝ) / q) ≤ Real.log 2 * e) :
    (P.card : ℝ) ≤ ((D : ℝ) + 1) * ((R : ℝ) + 1) * (2 : ℝ) ^ e := by
  have hDpos : 0 < (D : ℝ) := hq.trans_le hD
  have hbpos : 0 < 4 * (D : ℝ) / q := by positivity
  have hexp : (4 * (D : ℝ) / q) ^ q ≤ (2 : ℝ) ^ e := by
    rw [Real.rpow_def_of_pos hbpos, Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
    simpa only [mul_comm] using hbudget
  exact (card_paths_le_rpow_real P D R hq hD hR hdepth hB).trans
    (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- Appendix A.3, including floor division and the n=0 case, under its stated
fixed-parameter budget. This is an actual bound on finite path cardinality. -/
theorem card_paths_le_sparsification_exponential (P : Finset (List Bool))
    (C k n M : ℕ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.log (4 * (C : ℝ) * M / k) ≤ Real.log 2 / 32)
    (hdepth : ∀ p ∈ P, p.length ≤ C * n)
    (hB : ∀ p ∈ P, (bPositions p).card ≤ k * n / M) :
    (P.card : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) * ((k * n / M + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((n : ℝ) / 32) := by
  by_cases hn : n = 0
  · subst n
    have hcount := card_paths_le P (C * 0) (k * 0 / M) hdepth hB
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
      Real.log 2 * ((n : ℝ) / 32) := by
    rw [hbase]
    have h := mul_le_mul_of_nonneg_right hbudget hnpos.le
    convert h using 1 <;> first | (dsimp [q]; ring) | ring
  have h := card_paths_le_two_rpow P (C * n) (k * n / M) hq hD hR hdepth hB hb
  simpa only [Nat.cast_add, Nat.cast_one] using h

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree

/-- The exponential estimate applies to the actual number of tree nodes. -/
theorem Tree.nodeCount_le_sparsification_exponential (t : Tree)
    (C k n M : ℕ) (hk : 0 < k) (hM : 0 < M)
    (hDim : (k : ℝ) / M ≤ C)
    (hbudget : (k : ℝ) / M * Real.log (4 * (C : ℝ) * M / k) ≤ Real.log 2 / 32)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ C * n)
    (hB : ∀ p ∈ t.paths, (bPositions p).card ≤ k * n / M) :
    (t.nodeCount : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) * ((k * n / M + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((n : ℝ) / 32) := by
  rw [← t.card_paths]
  exact card_paths_le_sparsification_exponential t.paths C k n M hk hM
    hDim hbudget hdepth hB

/-- No analytic hypothesis remains once the constants module supplies its
integer admissibility certificate. The remaining premises are the two
combinatorial path bounds to be established for the sunflower process. -/
theorem Tree.nodeCount_le_of_admissible (t : Tree) (k n M : ℕ) (hk : 2 ≤ k)
    (hM : SparsificationConstants.Admissible k M)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ SparsificationConstants.C M (k - 1) * n)
    (hB : ∀ p ∈ t.paths, (bPositions p).card ≤ k * n / M) :
    (t.nodeCount : ℝ) ≤ ((SparsificationConstants.C M (k - 1) * n + 1 : ℕ) : ℝ) *
      ((k * n / M + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 32) := by
  exact t.nodeCount_le_sparsification_exponential
    (SparsificationConstants.C M (k - 1)) k n M (by omega)
    (by have := hM.1; omega) hM.ratio_le (hM.log_budget hk) hdepth hB

/-- The deterministic selected constants meet the exponent budget for every
input size. Their dependence on k is explicit; there is no n-dependent choice. -/
theorem Tree.nodeCount_le_chosen_parameters (t : Tree) (k n : ℕ) (hk : 2 ≤ k) :
    let M := SparsificationConstants.chooseM k hk
    let C := SparsificationConstants.C M (k - 1)
    (∀ p ∈ t.paths, p.length ≤ C * n) →
    (∀ p ∈ t.paths, (bPositions p).card ≤ k * n / M) →
    (t.nodeCount : ℝ) ≤ ((C * n + 1 : ℕ) : ℝ) * ((k * n / M + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((n : ℝ) / 32) := by
  dsimp
  intro hdepth hB
  exact t.nodeCount_le_of_admissible k n (SparsificationConstants.chooseM k hk) hk
    (SparsificationConstants.chooseM_spec k hk) hdepth hB

/-- The factor suppressed by `poly_k(n+1)` is at most a quadratic polynomial,
even without using M > 0. -/
theorem polynomial_prefactor_bound (C k n M : ℕ) :
    (C * n + 1) * (k * n / M + 1) ≤ (C + 1) * (k + 1) * (n + 1) ^ 2 := by
  have hdiv : k * n / M ≤ k * n := Nat.div_le_self _ _
  calc
    (C * n + 1) * (k * n / M + 1) ≤ (C * n + 1) * (k * n + 1) := by
      gcongr
    _ ≤ ((C + 1) * (n + 1)) * ((k + 1) * (n + 1)) := by
      apply Nat.mul_le_mul <;> nlinarith
    _ = (C + 1) * (k + 1) * (n + 1) ^ 2 := by ring

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree
open Finset

theorem bPositions_cons (b : Bool) (p : List Bool) :
    bPositions (b :: p) = (if b then {0} else ∅) ∪ (bPositions p).image Nat.succ := by
  ext i
  cases i with
  | zero => cases b <;> simp [mem_bPositions]
  | succ i => cases b <;> simp [mem_bPositions, mem_image]

theorem card_bPositions_cons (b : Bool) (p : List Bool) :
    (bPositions (b :: p)).card = (if b then 1 else 0) + (bPositions p).card := by
  rw [bPositions_cons]
  cases b <;> simp [card_image_of_injective _ Nat.succ_injective, Nat.add_comm]

theorem card_bPositions_eq_count (p : List Bool) :
    (bPositions p).card = p.count true := by
  induction p with
  | nil => simp [bPositions]
  | cons b p ih =>
    rw [card_bPositions_cons, ih]
    cases b <;> simp [Nat.add_comm]

end SubexponentialSAT.BranchTree

namespace SubexponentialSAT.BranchTree

/-- A concrete quadratic polynomial dominates all of the node-count prefactors. -/
theorem Tree.nodeCount_le_quadratic_exponential (t : Tree) (k n M : ℕ) (hk : 2 ≤ k)
    (hM : SparsificationConstants.Admissible k M)
    (hdepth : ∀ p ∈ t.paths, p.length ≤ SparsificationConstants.C M (k - 1) * n)
    (hB : ∀ p ∈ t.paths, p.count true ≤ k * n / M) :
    (t.nodeCount : ℝ) ≤
      (((SparsificationConstants.C M (k - 1) + 1) * (k + 1) * (n + 1) ^ 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((n : ℝ) / 32) := by
  have hcount := t.nodeCount_le_of_admissible k n M hk hM hdepth
    (fun p hp => by rw [card_bPositions_eq_count]; exact hB p hp)
  refine hcount.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _))
  exact_mod_cast polynomial_prefactor_bound (SparsificationConstants.C M (k - 1)) k n M

end SubexponentialSAT.BranchTree

end OAI.Algorithms
