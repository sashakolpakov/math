import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Counting
import OAI.Algorithms.SubexponentialSAT.Truncation
import OAI.Algorithms.SubexponentialSAT.GlobalPolynomial

namespace OAI.Algorithms

/-!
# Arbitrarily many factor groups and their local expansion

This file supplies the finite-color algebra in Section 4 of the subexponential
manuscript. A color partition is constructed by filtering the actual factor
indices. Products of separately truncated groups are compared with the full
product through canonical representatives, before substitution of X and U.
No hypothesis fixes the number of colors or assumes a final product identity.
-/

namespace SubexponentialSAT.SubexpGlobalPolynomial

noncomputable section

open scoped BigOperators

abbrev Poly (ι R : Type*) [CommSemiring R] := Truncation.Poly ι R

section Colors

variable {E G M : Type*} [Fintype E] [DecidableEq G]

/-- The actual factors assigned to one color. -/
def colorSet (color : E → G) (g : G) : Finset E :=
  Finset.univ.filter (fun e => color e = g)

@[simp] theorem mem_colorSet (color : E → G) (g : G) (e : E) :
    e ∈ colorSet color g ↔ color e = g := by
  simp [colorSet]

theorem colorSet_disjoint (color : E → G) {g h : G} (hgh : g ≠ h) :
    Disjoint (colorSet color g) (colorSet color h) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hgh ((mem_colorSet color g e).mp he |>.symm.trans
    ((mem_colorSet color h e).mp hf))

variable [Fintype G]

/-- Every factor occurs in exactly its own color group, including when some
color groups are empty. -/
theorem prod_colorSets [CommMonoid M] (color : E → G) (f : E → M) :
    (∏ g, ∏ e ∈ colorSet color g, f e) = ∏ e, f e := by
  exact Finset.prod_fiberwise Finset.univ color f

end Colors

section CanonicalProducts

variable {ι R G : Type*} [CommSemiring R]

theorem xTrunc_idempotent (N : ℕ) (P : MvPolynomial ι R) :
    Truncation.xTrunc N (Truncation.xTrunc N P) = Truncation.xTrunc N P := by
  classical
  ext a
  by_cases h : a.sum (fun _ k => k) ≤ N <;> simp [Truncation.coeff_xTrunc, h]

theorem canonical_idempotent (μ D N : ℕ) (P : Poly ι R) :
    Truncation.canonical μ D N (Truncation.canonical μ D N P) =
      Truncation.canonical μ D N P := by
  ext j r
  by_cases hj : j < μ <;> by_cases hr : r < D <;>
    simp [Truncation.coeff_canonical, hj, hr, xTrunc_idempotent]

/-- Canonical reduction can also be inserted on just one factor. -/
theorem canonical_mul_left (μ D N : ℕ) (P Q : Poly ι R) :
    Truncation.canonical μ D N (Truncation.canonical μ D N P * Q) =
      Truncation.canonical μ D N (P * Q) := by
  rw [← Truncation.canonical_mul μ D N (Truncation.canonical μ D N P) Q,
    canonical_idempotent, Truncation.canonical_mul]

theorem canonical_mul_right (μ D N : ℕ) (P Q : Poly ι R) :
    Truncation.canonical μ D N (P * Truncation.canonical μ D N Q) =
      Truncation.canonical μ D N (P * Q) := by
  rw [mul_comm P, canonical_mul_left, mul_comm Q]

/-- Any finite number of groups can be reduced separately before their
product is reduced. The assertion includes the empty product. -/
theorem canonical_prod (μ D N : ℕ) (s : Finset G) (P : G → Poly ι R) :
    Truncation.canonical μ D N (∏ g ∈ s, Truncation.canonical μ D N (P g)) =
      Truncation.canonical μ D N (∏ g ∈ s, P g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert g s hg ih =>
    simp only [Finset.prod_insert hg]
    calc
      Truncation.canonical μ D N
          (Truncation.canonical μ D N (P g) *
            ∏ h ∈ s, Truncation.canonical μ D N (P h)) =
          Truncation.canonical μ D N
            (Truncation.canonical μ D N (P g) *
              Truncation.canonical μ D N
                (∏ h ∈ s, Truncation.canonical μ D N (P h))) :=
        (canonical_mul_right μ D N _ _).symm
      _ = Truncation.canonical μ D N
            (Truncation.canonical μ D N (P g) *
              Truncation.canonical μ D N (∏ h ∈ s, P h)) := by rw [ih]
      _ = Truncation.canonical μ D N (P g * ∏ h ∈ s, P h) :=
        Truncation.canonical_mul μ D N _ _

/-- The arbitrary-group version of the canonical substitution theorem. -/
theorem truncated_groups_substitution (x : ι → R) (μ D : ℕ)
    (s : Finset G) (P : G → Poly ι R)
    (hP : ∀ g ∈ s, WeightedSupport.Admissible (P g))
    (hhigh : ∀ j, μ ≤ j →
      (Truncation.substX x (∏ g ∈ s, P g)).coeff j = 0) :
    Truncation.evalXU x
      (Truncation.canonical μ D (D + μ)
        (∏ g ∈ s, Truncation.canonical μ D (D + μ) (P g))) =
      Truncation.trunc D (Truncation.evalXU x (∏ g ∈ s, P g)) := by
  rw [canonical_prod]
  exact Truncation.canonical_substitution x μ D (D + μ) _ le_rfl
    (WeightedSupport.admissible_prod s P hP) hhigh

/-- The high-U condition can be derived from divisibility of the actual
substituted group polynomials and nilpotence, for any finite group count. -/
theorem truncated_groups_substitution_of_divisible (x : ι → R) (μ D : ℕ)
    (s : Finset G) (P : G → Poly ι R) (q : Polynomial R)
    (hP : ∀ g ∈ s, WeightedSupport.Admissible (P g)) (hnil : q ^ μ = 0)
    (hdiv : ∀ g ∈ s, NilpotentDefect.PowerDivisible q (Truncation.substX x (P g))) :
    Truncation.evalXU x
      (Truncation.canonical μ D (D + μ)
        (∏ g ∈ s, Truncation.canonical μ D (D + μ) (P g))) =
      Truncation.trunc D (Truncation.evalXU x (∏ g ∈ s, P g)) := by
  apply truncated_groups_substitution x μ D s P hP
  have hd : NilpotentDefect.PowerDivisible q
      (Truncation.substX x (∏ g ∈ s, P g)) := by
    rw [map_prod]
    exact NilpotentDefect.powerDivisible_prod q s _ hdiv
  exact NilpotentDefect.high_coeff_eq_zero hd hnil

end CanonicalProducts

section ColoredRows

variable {V E G Ω R : Type*} [CommRing R] [Fintype V] [Fintype E]
  [Fintype G] [DecidableEq G] {σ : E → Type*}

/-- Product of all concrete color groups is the full symbolic factor product. -/
theorem colored_rowGroup_product (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) :
    (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z) =
      Counting.rowGroup Finset.univ table row θ r β z := by
  exact prod_colorSets color _

/-- The canonical representative of the arbitrary color product has no
extra dependence on the chosen grouping. -/
theorem canonical_colored_rowGroup_product (μ D : ℕ) (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) :
    Truncation.canonical μ D (D + μ)
      (∏ g, Truncation.canonical μ D (D + μ)
        (Counting.rowGroup (colorSet color g) table row θ r β z)) =
      Truncation.canonical μ D (D + μ)
        (Counting.rowGroup Finset.univ table row θ r β z) := by
  rw [canonical_prod, colored_rowGroup_product]

/-- Local residue defects imply high-U vanishing of the whole color product;
the conclusion is not an assumed global nilpotence property. -/
theorem colored_rowGroup_highU (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) (x : V → R)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hβ : ∀ e i, p ∣
      MvPolynomial.eval x (Counting.rowCoefficient (row e i) θ 0) - β z e i)
    (j : ℕ) (hj : μ ≤ j) :
    (Truncation.substX x
      (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z)).coeff j = 0 := by
  rw [colored_rowGroup_product]
  exact Counting.rowGroup_highU Finset.univ table row θ r β z x p μ hnil
    (fun e _ i => hβ e i) j hj

/-- Lemma 4.1 for actual polynomial rows and arbitrarily many colors.
Admissibility and discarded high-U coefficients are derived from the row
construction and local residue defects. -/
theorem colored_rowGroups_truncation (μ D : ℕ) (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) (x : V → R)
    (p : R) (hnil : p ^ μ = 0)
    (hβ : ∀ e i, p ∣
      MvPolynomial.eval x (Counting.rowCoefficient (row e i) θ 0) - β z e i) :
    Truncation.evalXU x
      (Truncation.canonical μ D (D + μ)
        (∏ g, Truncation.canonical μ D (D + μ)
          (Counting.rowGroup (colorSet color g) table row θ r β z))) =
      Truncation.trunc D (Truncation.evalXU x
        (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z)) := by
  apply truncated_groups_substitution x μ D Finset.univ
    (fun g => Counting.rowGroup (colorSet color g) table row θ r β z)
  · intro g hg
    exact Counting.rowGroup_admissible _ table row θ r β z
  · exact colored_rowGroup_highU color table row θ r β z x p μ hnil hβ

/-- After evaluation, the product of the color groups is the actual shifted
factor product, independently of the residue-section values beta. -/
theorem evalXU_colored_rowGroups (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) (x : V → R)
    (hrow : ∀ e i w, (row e i w).natDegree ≤ r) :
    Truncation.evalXU x
      (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z) =
      ∏ e, GlobalPolynomial.compose (table e)
        (fun i => (GlobalPolynomial.rowValue (row e i) x).comp
          (Polynomial.X + Polynomial.C θ)) := by
  rw [colored_rowGroup_product]
  exact Counting.evalXU_rowGroup Finset.univ table row θ r β z x
    (fun e _ i w => hrow e i w)

variable [Fintype Ω]

/-- Sum over inputs gives the local expansion of the actual global H. -/
theorem sum_evalXU_colored_rowGroups (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (v : Ω → V → R)
    (hrow : ∀ e i w, (row e i w).natDegree ≤ r) :
    (∑ z, Truncation.evalXU (v z)
      (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z)) =
      (GlobalPolynomial.globalPolynomial table
        (fun z e i => GlobalPolynomial.rowValue (row e i) (v z))).comp
          (Polynomial.X + Polynomial.C θ) := by
  classical
  rw [GlobalPolynomial.comp_globalPolynomial]
  unfold GlobalPolynomial.globalPolynomial
  apply Finset.sum_congr rfl
  intro z hz
  exact evalXU_colored_rowGroups color table row θ r β z (v z) hrow

/-- Truncating the evaluated sum yields the requested length-D jet. -/
theorem sum_trunc_evalXU_colored_rowGroups (D : ℕ) (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (v : Ω → V → R)
    (hrow : ∀ e i w, (row e i w).natDegree ≤ r) :
    (∑ z, Truncation.trunc D (Truncation.evalXU (v z)
      (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z))) =
      Truncation.trunc D
        ((GlobalPolynomial.globalPolynomial table
          (fun z e i => GlobalPolynomial.rowValue (row e i) (v z))).comp
            (Polynomial.X + Polynomial.C θ)) := by
  have h := congrArg (Truncation.truncAddHom (A := R) D)
    (sum_evalXU_colored_rowGroups color table row θ r β v hrow)
  rw [map_sum] at h
  change (∑ z, Truncation.trunc D (Truncation.evalXU (v z)
    (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z))) =
    Truncation.trunc D
      ((GlobalPolynomial.globalPolynomial table
        (fun z e i => GlobalPolynomial.rowValue (row e i) (v z))).comp
          (Polynomial.X + Polynomial.C θ)) at h
  exact h

/-- Full arbitrary-color truncation-to-global-jet identity. The groups are
reduced before their product and before evaluating X and U; all hypotheses
are local row bounds, local p-divisibility, and p^μ = 0. -/
theorem sum_canonical_colored_rowGroups (μ D : ℕ) (color : E → G)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (v : Ω → V → R)
    (hrow : ∀ e i w, (row e i w).natDegree ≤ r)
    (p : R) (hnil : p ^ μ = 0)
    (hβ : ∀ z e i, p ∣
      MvPolynomial.eval (v z) (Counting.rowCoefficient (row e i) θ 0) - β z e i) :
    (∑ z, Truncation.evalXU (v z)
      (Truncation.canonical μ D (D + μ)
        (∏ g, Truncation.canonical μ D (D + μ)
          (Counting.rowGroup (colorSet color g) table row θ r β z)))) =
      Truncation.trunc D
        ((GlobalPolynomial.globalPolynomial table
          (fun z e i => GlobalPolynomial.rowValue (row e i) (v z))).comp
            (Polynomial.X + Polynomial.C θ)) := by
  classical
  calc
    _ = ∑ z, Truncation.trunc D (Truncation.evalXU (v z)
        (∏ g, Counting.rowGroup (colorSet color g) table row θ r β z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact colored_rowGroups_truncation μ D color table row θ r β z (v z) p hnil (hβ z)
    _ = _ := sum_trunc_evalXU_colored_rowGroups D color table row θ r β v hrow

end ColoredRows

end

end SubexponentialSAT.SubexpGlobalPolynomial

end OAI.Algorithms
