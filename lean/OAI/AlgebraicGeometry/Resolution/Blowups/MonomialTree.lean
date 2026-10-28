import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTermination
import Mathlib.Data.Finset.Lattice.Fold

/-! # Monomial Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTree.Construction

noncomputable section

/-! Finite local resolution trees for a positive-control monomial ideal. -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A local monomial resolution tree. Each internal node uses a minimal
permissible coordinate center and includes all its denominator charts.
Leaves have total exponent below the chosen control. -/
inductive MonomialResolutionTree (b : ℕ) : (σ → ℕ) → Type _
  | done (a : σ → ℕ) (ha : (∑ j, a j) < b) : MonomialResolutionTree b a
  | blowup (a : σ → ℕ) (C : Finset σ) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C)
      (children : ∀ i : C, MonomialResolutionTree b (MonomialTermination.Construction.monomialChartExponents a b C i.val)) :
      MonomialResolutionTree b a

/-- Construct the tree by the proved well-founded exponent relation. -/
def monomialResolutionTree (b : ℕ) (hb : 0 < b) (a : σ → ℕ) : Construction.MonomialResolutionTree b a :=
  (MonomialTermination.Construction.monomialControlledStep_wellFounded b).fix (fun a rec =>
    if ha : (∑ j, a j) < b then .done a ha else
      let hex := MonomialTermination.Construction.exists_minimal_monomial_center a b hb Finset.univ (Nat.le_of_not_gt ha)
      let C := hex.choose
      let hC := hex.choose_spec.2
      .blowup a C hC (fun i => rec (MonomialTermination.Construction.monomialChartExponents a b C i.val)
        ⟨C, i.val, hC, i.property, rfl⟩)) a

/-- The number of successive blowups along the longest branch. -/
def MonomialResolutionTree.height {b : ℕ} {a : σ → ℕ} : Construction.MonomialResolutionTree b a → ℕ
  | .done _ _ => 0
  | .blowup _ _ _ children => (Finset.univ.sup fun i => (children i).height) + 1

/-- The entire finite tree has branch length bounded by the original
sum of exponents, independently of which minimal centers are selected. -/
theorem MonomialResolutionTree.height_le {b : ℕ} {a : σ → ℕ} (T : Construction.MonomialResolutionTree b a) :
    T.height ≤ ∑ j, a j := by
  induction T with
  | done a ha => exact Nat.zero_le _
  | blowup a C hC children ih =>
    change (Finset.univ.sup fun i => (children i).height) + 1 ≤ ∑ j, a j
    obtain ⟨i, hi⟩ := hC.1
    have hpos := MonomialTermination.Construction.monomialChartExponents_sum_lt a b C hC i hi
    have hsup : (Finset.univ.sup fun i => (children i).height) ≤ (∑ j, a j) - 1 := by
      apply Finset.sup_le
      intro i _
      have hlt := MonomialTermination.Construction.monomialChartExponents_sum_lt a b C hC i.val i.property
      have hle := ih i
      omega
    omega

/-- Positive-control monomial ideals admit finite local resolution trees
with an explicit natural-number bound on every branch. -/
theorem exists_bounded_monomial_resolution_tree (b : ℕ) (hb : 0 < b) (a : σ → ℕ) :
    ∃ T : Construction.MonomialResolutionTree b a, T.height ≤ ∑ j, a j :=
  ⟨monomialResolutionTree b hb a, Construction.MonomialResolutionTree.height_le _⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTree.Construction
