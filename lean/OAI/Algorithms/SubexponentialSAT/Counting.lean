import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Truncation
import OAI.Algorithms.SubexponentialSAT.Moments
import OAI.Algorithms.SubexponentialSAT.Separation
import OAI.Algorithms.SubexponentialSAT.GlobalPolynomial
import OAI.Algorithms.SubexponentialSAT.JetCRT
import OAI.Algorithms.SubexponentialSAT.LiftRing
import OAI.Algorithms.SubexponentialSAT.NilpotentDefect
import OAI.Algorithms.SubexponentialSAT.LayoutSpec
import OAI.Algorithms.SubexponentialSAT.Incidence
import OAI.Algorithms.SubexponentialSAT.TruncatedInverse
import OAI.Algorithms.SubexponentialSAT.ActualLiftRing

namespace OAI.Algorithms

/-!
# Exact counting by separated symbolic moments

This module defines the separated finite sums, rather than assuming they
return the target count. Canonical deletion is applied before coefficient
extraction and before evaluating U at one. Theorems make the algebraic
hypotheses explicit; they do not claim an executable bit-complexity bound.
-/

namespace SubexponentialSAT.Counting

noncomputable section

open scoped BigOperators

abbrev Poly (ι R : Type*) [CommSemiring R] := Truncation.Poly ι R

section Local

variable {ι Ω O R : Type*} {X Y : O → Type*}
  [CommSemiring R] [Fintype ι] [Fintype Ω] [Fintype O]
  [∀ o, Fintype (X o)] [∀ o, Fintype (Y o)]

/-- A group polynomial after deleting precisely the forbidden monomials. -/
def group (μ D : ℕ) (P : Ω → Poly ι R) (z : Ω) : Poly ι R :=
  Truncation.canonical μ D (D + μ) (P z)

/-- The canonical product of the two separately truncated groups. -/
def groupProduct (μ D : ℕ) (P Q : Ω → Poly ι R) (z : Ω) : Poly ι R :=
  Truncation.canonical μ D (D + μ) (group μ D P z * group μ D Q z)

/-- The actual two inner sums of equation (4.8), followed by canonical
reduction of the result. The input equivalence enumerates every assignment
exactly once by outer data and two fibers. -/
def separatedMoment (μ D : ℕ) (e : Ω ≃ Σ o, X o × Y o)
    (r₀ : ∀ o, X o) (r₁ : ∀ o, Y o) (P Q : Ω → Poly ι R)
    (c : O → R) (w₀ : ∀ o, X o → R) (w₁ : ∀ o, Y o → R) : Poly ι R :=
  Truncation.canonical μ D (D + μ)
    (∑ o, WeightedSupport.scalarHom (c o) *
      (∑ x : X o, WeightedSupport.scalarHom (w₀ o x) *
        group μ D Q (e.symm ⟨o, x, r₁ o⟩)) *
      (∑ y : Y o, WeightedSupport.scalarHom (w₁ o y) *
        group μ D P (e.symm ⟨o, r₀ o, y⟩)))

/-- Extract the X monomial while retaining both polynomial variables U,Z. -/
def extractX (a : ι →₀ ℕ) : Poly ι R →+ Polynomial (Polynomial R) :=
  Truncation.mapCoeffs (Truncation.mapCoeffs (MvPolynomial.coeffAddMonoidHom a))

/-- Equation (4.7), with all moment sums actually given by the separated
construction. U=1 is applied only after canonical reduction and extraction. -/
def separatedJet (μ D : ℕ) (e : Ω ≃ Σ o, X o × Y o)
    (r₀ : ∀ o, X o) (r₁ : ∀ o, Y o) (P Q : Ω → Poly ι R)
    (c : (ι →₀ ℕ) → O → R)
    (w₀ : (ι →₀ ℕ) → ∀ o, X o → R)
    (w₁ : (ι →₀ ℕ) → ∀ o, Y o → R) : Polynomial R :=
  ∑ a ∈ Moments.retained (D + μ),
    (extractX a (separatedMoment μ D e r₀ r₁ P Q (c a) (w₀ a) (w₁ a))).eval 1

omit [Fintype ι] [Fintype Ω] in
/-- The product used in moment extraction equals the canonical reduction of
the full product, even though the two groups were truncated independently. -/
theorem groupProduct_eq (μ D : ℕ) (P Q : Ω → Poly ι R) (z : Ω) :
    groupProduct μ D P Q z = Truncation.canonical μ D (D + μ) (P z * Q z) := by
  exact Truncation.canonical_mul μ D (D + μ) (P z) (Q z)

omit [Fintype ι] [Fintype Ω] in
/-- Exact group invariance passes through canonical truncation. -/
theorem group_congr (μ D : ℕ) (P : Ω → Poly ι R) {z z' : Ω}
    (h : P z = P z') : group μ D P z = group μ D P z' := congrArg (Truncation.canonical μ D (D + μ)) h

omit [Fintype ι] in
/-- No target-count equality is assumed: the unsimplified separated sum is
proved equal to the full symbolic moment by finite distributivity. -/
theorem separatedMoment_eq_canonical_sum (μ D : ℕ)
    (e : Ω ≃ Σ o, X o × Y o) (r₀ : ∀ o, X o) (r₁ : ∀ o, Y o)
    (P Q : Ω → Poly ι R) (w : Ω → R)
    (c : O → R) (w₀ : ∀ o, X o → R) (w₁ : ∀ o, Y o → R)
    (hP : ∀ o x x' y, P (e.symm ⟨o, x, y⟩) = P (e.symm ⟨o, x', y⟩))
    (hQ : ∀ o x y y', Q (e.symm ⟨o, x, y⟩) = Q (e.symm ⟨o, x, y'⟩))
    (hw : ∀ o x y, w (e.symm ⟨o, x, y⟩) = c o * w₀ o x * w₁ o y) :
    separatedMoment μ D e r₀ r₁ P Q c w₀ w₁ =
      Truncation.canonical μ D (D + μ)
        (∑ z, WeightedSupport.scalarHom (w z) * group μ D P z * group μ D Q z) := by
  unfold separatedMoment
  congr 1
  symm
  apply Separation.weighted_separation_equiv e r₀ r₁
    (group μ D P) (group μ D Q) (fun z => WeightedSupport.scalarHom (w z))
    (fun o => WeightedSupport.scalarHom (c o))
    (fun o x => WeightedSupport.scalarHom (w₀ o x))
    (fun o y => WeightedSupport.scalarHom (w₁ o y))
  · intro o x x' y
    exact group_congr μ D P (hP o x x' y)
  · intro o x y y'
    exact group_congr μ D Q (hQ o x y y')
  · intro o x y
    rw [hw, map_mul, map_mul]

omit [Fintype ι] in
/-- Moving canonical reduction through the finite sums and scalar weights
identifies the separated output with the full moment of canonical products. -/
theorem separatedMoment_eq_sum (μ D : ℕ)
    (e : Ω ≃ Σ o, X o × Y o) (r₀ : ∀ o, X o) (r₁ : ∀ o, Y o)
    (P Q : Ω → Poly ι R) (w : Ω → R)
    (c : O → R) (w₀ : ∀ o, X o → R) (w₁ : ∀ o, Y o → R)
    (hP : ∀ o x x' y, P (e.symm ⟨o, x, y⟩) = P (e.symm ⟨o, x', y⟩))
    (hQ : ∀ o x y y', Q (e.symm ⟨o, x, y⟩) = Q (e.symm ⟨o, x, y'⟩))
    (hw : ∀ o x y, w (e.symm ⟨o, x, y⟩) = c o * w₀ o x * w₁ o y) :
    separatedMoment μ D e r₀ r₁ P Q c w₀ w₁ =
      ∑ z, WeightedSupport.scalarHom (w z) * groupProduct μ D P Q z := by
  rw [separatedMoment_eq_canonical_sum μ D e r₀ r₁ P Q w c w₀ w₁ hP hQ hw,
    Truncation.canonical_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [mul_assoc, Truncation.canonical_scalar_mul]
  rfl

/-- Every retained coefficient really has support in the finite moment set. -/
theorem canonical_support (μ D N j r : ℕ) (P : Poly ι R) :
    (((Truncation.canonical μ D N P).coeff j).coeff r).support ⊆
      Moments.retained N := by
  intro a ha
  rw [Moments.mem_retained]
  by_contra h
  have hc := MvPolynomial.mem_support_iff.mp ha
  apply hc
  rw [Truncation.coeff_canonical]
  split_ifs
  · simp [Truncation.coeff_xTrunc, h]
  · simp

omit [Fintype ι] [Fintype Ω] in
/-- Exact substitution of the canonical group product is the desired local
truncation; the two hypotheses are support filtration and nilpotence. -/
theorem groupProduct_substitution (μ D : ℕ) (P Q : Ω → Poly ι R)
    (v : Ω → ι → R)
    (hP : ∀ z, WeightedSupport.Admissible (P z))
    (hQ : ∀ z, WeightedSupport.Admissible (Q z))
    (hhigh : ∀ z j, μ ≤ j → (Truncation.substX (v z) (P z * Q z)).coeff j = 0)
    (z : Ω) :
    Truncation.evalXU (v z) (groupProduct μ D P Q z) =
      Truncation.trunc D (Truncation.evalXU (v z) (P z * Q z)) := by
  exact Truncation.truncated_groups_substitution (v z) μ D (P z) (Q z)
    (hP z) (hQ z) (hhigh z)

/-- The defined separated-jet construction is the sum of the correct local
truncations. Its hypotheses concern input invariance, scalar weights, support,
and nilpotence; no equality with the desired jet is assumed. -/
theorem separatedJet_eq_sum (μ D : ℕ)
    (e : Ω ≃ Σ o, X o × Y o) (r₀ : ∀ o, X o) (r₁ : ∀ o, Y o)
    (P Q : Ω → Poly ι R) (v : Ω → ι → R)
    (c : (ι →₀ ℕ) → O → R)
    (w₀ : (ι →₀ ℕ) → ∀ o, X o → R)
    (w₁ : (ι →₀ ℕ) → ∀ o, Y o → R)
    (hP : ∀ o x x' y, P (e.symm ⟨o, x, y⟩) = P (e.symm ⟨o, x', y⟩))
    (hQ : ∀ o x y y', Q (e.symm ⟨o, x, y⟩) = Q (e.symm ⟨o, x, y'⟩))
    (hw : ∀ a o x y, Moments.weight a (v (e.symm ⟨o, x, y⟩)) =
      c a o * w₀ a o x * w₁ a o y)
    (hPa : ∀ z, WeightedSupport.Admissible (P z))
    (hQa : ∀ z, WeightedSupport.Admissible (Q z))
    (hhigh : ∀ z j, μ ≤ j → (Truncation.substX (v z) (P z * Q z)).coeff j = 0) :
    separatedJet μ D e r₀ r₁ P Q c w₀ w₁ =
      ∑ z, Truncation.trunc D (Truncation.evalXU (v z) (P z * Q z)) := by
  classical
  calc
    separatedJet μ D e r₀ r₁ P Q c w₀ w₁ =
        ∑ a ∈ Moments.retained (D + μ),
          (extractX a (∑ z, WeightedSupport.scalarHom (Moments.weight a (v z)) *
            groupProduct μ D P Q z)).eval 1 := by
      unfold separatedJet
      apply Finset.sum_congr rfl
      intro a ha
      rw [separatedMoment_eq_sum μ D e r₀ r₁ P Q
        (fun z => Moments.weight a (v z)) (c a) (w₀ a) (w₁ a) hP hQ (hw a)]
    _ = ∑ z, Truncation.evalXU (v z) (groupProduct μ D P Q z) := by
      exact Moments.sum_retained_nested_moments_eval_one_eq_sum_evalXU
        (D + μ) (groupProduct μ D P Q) v
        (fun z j r => canonical_support μ D (D + μ) j r _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact groupProduct_substitution μ D P Q v hPa hQa hhigh z

end Local

section Rows

variable {V E Ω R : Type*} [CommRing R] [Fintype V] {σ : E → Type*}

/-- The coefficient of Z^j in a shifted row, kept as an actual linear form
in the formal input variables. -/
def rowCoefficient (row : V → Polynomial R) (θ : R) (j : ℕ) : MvPolynomial V R :=
  WeightedSupport.linearForm Finset.univ
    (fun v => ((row v).comp (Polynomial.X + Polynomial.C θ)).coeff j)

/-- The manuscript's incidence argument, with the positive-Z expansion
constructed directly from the polynomial row. -/
def rowArgument (row : V → Polynomial R) (θ β : R) (r : ℕ) : Poly V R :=
  WeightedSupport.incidenceArgument β (rowCoefficient row θ 0)
    ((Finset.range (r + 1)).erase 0) (rowCoefficient row θ)

theorem rowArgument_admissible (row : V → Polynomial R) (θ β : R) (r : ℕ) :
    WeightedSupport.Admissible (rowArgument row θ β r) := by
  apply WeightedSupport.admissible_incidence_linearForms
  intro j hj
  exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hj).1

/-- Substitution cancels beta and reconstructs the shifted scalar row. -/
theorem evalXU_rowArgument (row : V → Polynomial R) (x : V → R)
    (θ β : R) (r : ℕ) (hrow : ∀ v, (row v).natDegree ≤ r) :
    Truncation.evalXU x (rowArgument row θ β r) =
      (GlobalPolynomial.rowValue row x).comp (Polynomial.X + Polynomial.C θ) := by
  rw [rowArgument, Truncation.evalXU_incidenceArgument]
  exact (GlobalPolynomial.shifted_rowValue_expansion row x θ r hrow).symm

/-- A full symbolic factor group. Its dependence on the actual input z is
confined to beta; every rowCoefficient remains a formal polynomial. -/
def rowGroup (s : Finset E) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) : Poly V R :=
  ∏ e ∈ s, MvPolynomial.eval₂ (WeightedSupport.scalarHom (ι := V))
    (fun i => rowArgument (row e i) θ (β z e i) r) (table e)

theorem rowGroup_admissible (s : Finset E) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) :
    WeightedSupport.Admissible (rowGroup s table row θ r β z) := by
  apply WeightedSupport.admissible_factor_product
  intro e he i
  exact rowArgument_admissible (row e i) θ (β z e i) r

theorem rowGroup_congr (s : Finset E) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) {z z' : Ω}
    (hβ : ∀ e ∈ s, ∀ i, β z e i = β z' e i) :
    rowGroup s table row θ r β z = rowGroup s table row θ r β z' := by
  apply Finset.prod_congr rfl
  intro e he
  congr 1
  funext i
  rw [hβ e he i]

/-- Evaluation of an entire symbolic group is its shifted factor product. -/
theorem evalXU_rowGroup (s : Finset E) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) (x : V → R)
    (hrow : ∀ e ∈ s, ∀ i v, (row e i v).natDegree ≤ r) :
    Truncation.evalXU x (rowGroup s table row θ r β z) =
      ∏ e ∈ s, GlobalPolynomial.compose (table e)
        (fun i => (GlobalPolynomial.rowValue (row e i) x).comp
          (Polynomial.X + Polynomial.C θ)) := by
  rw [rowGroup, Truncation.evalXU_factor_product]
  apply Finset.prod_congr rfl
  intro e he
  congr 1
  funext i
  exact evalXU_rowArgument (row e i) x θ (β z e i) r (hrow e he i)

/-- Disjoint factor groups multiply to the full group. -/
theorem rowGroup_union [DecidableEq E] (s t : Finset E) (hst : Disjoint s t)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) :
    rowGroup (s ∪ t) table row θ r β z =
      rowGroup s table row θ r β z * rowGroup t table row θ r β z :=
  Finset.prod_union hst

/-- Prime-power divisibility kills every discarded U coefficient for the
actual row/table construction; it is not assumed for the final product. -/
theorem rowGroup_highU (s : Finset E) (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (z : Ω) (x : V → R)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hβ : ∀ e ∈ s, ∀ i, p ∣ MvPolynomial.eval x (rowCoefficient (row e i) θ 0) - β z e i)
    (j : ℕ) (hj : μ ≤ j) :
    (Truncation.substX x (rowGroup s table row θ r β z)).coeff j = 0 := by
  exact NilpotentDefect.highU_factor_product x p μ hnil s table (β z)
    (fun e i => rowCoefficient (row e i) θ 0)
    (fun _ _ => (Finset.range (r + 1)).erase 0)
    (fun e i => rowCoefficient (row e i) θ) hβ j hj

end Rows

section GlobalRows

variable {V E Ω R : Type*} [CommRing R] [Fintype V] [Fintype E] [DecidableEq E]
  [Fintype Ω] {σ : E → Type*}

/-- The two actual symbolic factor groups give exactly the formal expansion
of H at the chosen node after X substitution and U=1. -/
theorem sum_evalXU_rowGroups (s t : Finset E) (hst : Disjoint s t)
    (hcover : s ∪ t = Finset.univ)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (v : Ω → V → R)
    (hrow : ∀ e i w, (row e i w).natDegree ≤ r) :
    (∑ z, Truncation.evalXU (v z)
      (rowGroup s table row θ r β z * rowGroup t table row θ r β z)) =
      (GlobalPolynomial.globalPolynomial table
        (fun z e i => GlobalPolynomial.rowValue (row e i) (v z))).comp
          (Polynomial.X + Polynomial.C θ) := by
  classical
  rw [GlobalPolynomial.comp_globalPolynomial]
  unfold GlobalPolynomial.globalPolynomial
  apply Finset.sum_congr rfl
  intro z hz
  rw [← rowGroup_union s t hst, hcover]
  exact evalXU_rowGroup Finset.univ table row θ r β z (v z)
    (fun e _ i w => hrow e i w)

/-- The correct local jet expressed as the sum of the truncated group
substitutions, before the moment-separation optimization is invoked. -/
theorem sum_trunc_evalXU_rowGroups (_μ D : ℕ)
    (s t : Finset E) (hst : Disjoint s t) (hcover : s ∪ t = Finset.univ)
    (table : ∀ e, MvPolynomial (σ e) R)
    (row : ∀ e, σ e → V → Polynomial R) (θ : R) (r : ℕ)
    (β : Ω → ∀ e, σ e → R) (v : Ω → V → R)
    (hrow : ∀ e i w, (row e i w).natDegree ≤ r) :
    (∑ z, Truncation.trunc D (Truncation.evalXU (v z)
      (rowGroup s table row θ r β z * rowGroup t table row θ r β z))) =
      Truncation.trunc D
        ((GlobalPolynomial.globalPolynomial table
          (fun z e i => GlobalPolynomial.rowValue (row e i) (v z))).comp
            (Polynomial.X + Polynomial.C θ)) := by
  have h := congrArg (Truncation.truncAddHom (A := R) D)
    (sum_evalXU_rowGroups s t hst hcover table row θ r β v hrow)
  rw [map_sum] at h
  exact h

end GlobalRows

section TruncationBridge

variable {R : Type*} [CommRing R]

/-- Canonical coefficient deletion agrees with monic reduction modulo Z^D. -/
theorem trunc_eq_modByMonic (D : ℕ) (f : Polynomial R) :
    Truncation.trunc D f = f %ₘ (Polynomial.X ^ D) := by
  nontriviality R
  have hdiv : (Polynomial.X : Polynomial R) ^ D ∣ f - Truncation.trunc D f := by
    rw [Polynomial.X_pow_dvd_iff]
    intro n hn
    simp [Truncation.coeff_trunc, hn]
  have hself : Truncation.trunc D f %ₘ (Polynomial.X ^ D) = Truncation.trunc D f := by
    apply (Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X.pow D)).2
    rw [Polynomial.degree_X_pow]
    apply (Polynomial.degree_lt_iff_coeff_zero _ D).2
    intro n hn
    simp [Truncation.coeff_trunc, Nat.not_lt.mpr hn]
  exact ((Polynomial.modByMonic_eq_of_dvd_sub (Polynomial.monic_X.pow D) hdiv).trans hself).symm

theorem jet_eq_trunc (θ : R) (D : ℕ) (f : Polynomial R) :
    JetCRT.jet θ D f = Truncation.trunc D (f.comp (Polynomial.X + Polynomial.C θ)) := by
  exact (trunc_eq_modByMonic D _).symm

end TruncationBridge

section LayoutCounting

variable {p k Δ : ℕ} [Fact p.Prime]
  {V F K R : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] {P : Factor.Pattern V F} {c : LayoutSpec.Constants p k Δ}
  {L : LayoutSpec.Layout (E := K) P c}

/-- The actual residue lift used as beta at each incidence. -/
def layoutBeta (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue) (t : Fin c.Q)
    (x : V → ZMod p) (e : F) (i : {v // v ∈ P.scope e}) : R :=
  (A.liftedRow lift hLift t e i).beta s x

/-- Factor colors determine the two concrete groups. -/
def colorGroup (L : LayoutSpec.Layout (E := K) P c) (t : Fin c.Q) (g : Bool) : Finset F :=
  Finset.univ.filter (fun e => L.color e t = g)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem colorGroup_disjoint (L : LayoutSpec.Layout (E := K) P c) (t : Fin c.Q) :
    Disjoint (colorGroup L t false) (colorGroup L t true) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  simp only [colorGroup, Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  rw [he] at hf
  cases hf

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem colorGroup_union (L : LayoutSpec.Layout (E := K) P c) (t : Fin c.Q) :
    colorGroup L t false ∪ colorGroup L t true = Finset.univ := by
  ext e
  simp only [colorGroup, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  cases L.color e t <;> simp

/-- The actual symbolic groups determined by a lifted layout. -/
def layoutGroup (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (t : Fin c.Q) (g : Bool) : (V → ZMod p) → Poly V R :=
  rowGroup (colorGroup L t g) table A.row (A.theta t) c.R
    (layoutBeta A lift hLift s t)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem layoutGroup_left_invariant (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R) (t : Fin c.Q)
    (o : L.Outer t) (x x' : L.Left t o) (y : L.Right t o) :
    layoutGroup A lift hLift s table t false (L.reconstruct t o x y) =
      layoutGroup A lift hLift s table t false (L.reconstruct t o x' y) := by
  apply rowGroup_congr
  intro e he i
  exact A.beta_reconstruct_left lift hLift s t e i
    (Finset.mem_filter.mp he).2 o x x' y

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem layoutGroup_right_invariant (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R) (t : Fin c.Q)
    (o : L.Outer t) (x : L.Left t o) (y y' : L.Right t o) :
    layoutGroup A lift hLift s table t true (L.reconstruct t o x y) =
      layoutGroup A lift hLift s table t true (L.reconstruct t o x y') := by
  apply rowGroup_congr
  intro e he i
  exact A.beta_reconstruct_right lift hLift s t e i
    (Finset.mem_filter.mp he).2 o x y y'

omit [DecidableEq V] in
/-- The constant coefficient used in the symbolic argument is exactly the
actual lifted row value, before selecting beta. -/
theorem eval_rowCoefficient_zero (row : V → Polynomial R) (x : V → R) (θ : R) :
    MvPolynomial.eval x (rowCoefficient row θ 0) = ∑ w, (row w).eval θ * x w := by
  classical
  simp [rowCoefficient, WeightedSupport.linearForm, MvPolynomial.eval_monomial,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, mul_comm]

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The local p-divisibility hypothesis is derived from the actual residue
kernel and the chosen section. -/
theorem layoutBeta_defect (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (t : Fin c.Q) (x : V → ZMod p) (e : F) (i : {v // v ∈ P.scope e}) :
    (p : R) ∣ MvPolynomial.eval (fun w => lift (x w))
      (rowCoefficient (A.row e i) (A.theta t) 0) - layoutBeta A lift hLift s t x e i := by
  rw [eval_rowCoefficient_zero]
  exact (A.liftedRow lift hLift t e i).value_sub_beta_dvd s (p : R) hker x

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- A concrete point in a nonempty coset, chosen independently of all weights. -/
def cosetRepresentative {𝔽 M : Type*} [Field 𝔽] [AddCommGroup M] [Module 𝔽 M]
    (U : Submodule 𝔽 M) (q : M ⧸ U) : CosetCardinality.CosetFiber U q :=
  ⟨Classical.choose (Submodule.Quotient.mk_surjective (p := U) q),
    Classical.choose_spec (Submodule.Quotient.mk_surjective (p := U) q)⟩

def layoutOuterWeight (L : LayoutSpec.Layout (E := K) P c) (lift : ZMod p → R)
    (t : Fin c.Q) (a : V →₀ ℕ) (o : L.Outer t) : R :=
  ∏ i : ↥((L.support t false ∪ L.support t true)ᶜ), lift (o.1 i) ^ a i.val

def layoutLeftWeight (L : LayoutSpec.Layout (E := K) P c) (lift : ZMod p → R)
    (t : Fin c.Q) (a : V →₀ ℕ) (o : L.Outer t) (x : L.Left t o) : R :=
  ∏ i : L.support t false, lift (x.val i) ^ a i.val

def layoutRightWeight (L : LayoutSpec.Layout (E := K) P c) (lift : ZMod p → R)
    (t : Fin c.Q) (a : V →₀ ℕ) (o : L.Outer t) (y : L.Right t o) : R :=
  ∏ i : L.support t true, lift (y.val i) ^ a i.val

local instance leftFintype (t : Fin c.Q) (o : L.Outer t) : Fintype (L.Left t o) := by
  classical
  unfold LayoutSpec.Layout.Left CosetCardinality.CosetFiber
  infer_instance

local instance rightFintype (t : Fin c.Q) (o : L.Outer t) : Fintype (L.Right t o) := by
  classical
  unfold LayoutSpec.Layout.Right CosetCardinality.CosetFiber
  infer_instance

/-- The complete separated local computation, with groups, representatives,
weights, and outer/inner domains supplied by the actual layout. -/
def layoutJet (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (t : Fin c.Q) : Polynomial R := by
  classical
  exact separatedJet μ D (L.coordinateOuterFiberEquiv t)
    (fun o => cosetRepresentative (L.localK t false) o.2.1)
    (fun o => cosetRepresentative (L.localK t true) o.2.2)
    (layoutGroup A lift hLift s table t false)
    (layoutGroup A lift hLift s table t true)
    (layoutOuterWeight L lift t) (layoutLeftWeight L lift t) (layoutRightWeight L lift t)

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- All semantic hypotheses of the separated-jet theorem are discharged by
the actual layout, residue kernel, and nilpotence. -/
theorem layoutJet_eq (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (t : Fin c.Q) :
    layoutJet A lift hLift s table μ D t =
      JetCRT.jet (A.theta t) D
        (GlobalPolynomial.rowGlobalPolynomial table A.row lift) := by
  classical
  calc
    layoutJet A lift hLift s table μ D t =
        ∑ x : V → ZMod p, Truncation.trunc D
          (Truncation.evalXU (fun w => lift (x w))
            (layoutGroup A lift hLift s table t false x *
              layoutGroup A lift hLift s table t true x)) := by
      unfold layoutJet
      refine separatedJet_eq_sum (ι := V) (Ω := V → ZMod p) (O := L.Outer t)
        (X := L.Left t) (Y := L.Right t) (R := R) μ D
        (L.coordinateOuterFiberEquiv t)
        (fun o => cosetRepresentative (L.localK t false) o.2.1)
        (fun o => cosetRepresentative (L.localK t true) o.2.2)
        (layoutGroup A lift hLift s table t false)
        (layoutGroup A lift hLift s table t true) (fun x w => lift (x w))
        (layoutOuterWeight L lift t) (layoutLeftWeight L lift t)
        (layoutRightWeight L lift t) ?_ ?_ ?_ ?_ ?_ ?_
      · exact layoutGroup_left_invariant A lift hLift s table t
      · exact layoutGroup_right_invariant A lift hLift s table t
      · intro a o x y
        exact Separation.momentWeight_coordinateReconstruct
          (L.support t false) (L.support t true) (L.support_disjoint t)
          (L.localK t false) (L.localK t true) o x y a lift
      · intro x
        exact rowGroup_admissible _ _ _ _ _ _ _
      · intro x
        exact rowGroup_admissible _ _ _ _ _ _ _
      · intro x j hj
        change (Truncation.substX (fun w => lift (x w))
          (rowGroup (colorGroup L t false) table A.row (A.theta t) c.R
            (layoutBeta A lift hLift s t) x *
           rowGroup (colorGroup L t true) table A.row (A.theta t) c.R
            (layoutBeta A lift hLift s t) x)).coeff j = 0
        rw [← rowGroup_union _ _ (colorGroup_disjoint L t), colorGroup_union]
        exact rowGroup_highU Finset.univ table A.row (A.theta t) c.R
          (layoutBeta A lift hLift s t) x (fun w => lift (x w)) (p : R) μ hnil
          (fun e _ i => layoutBeta_defect A lift hLift s hker t x e i) j hj
    _ = JetCRT.jet (A.theta t) D
        (GlobalPolynomial.rowGlobalPolynomial table A.row lift) := by
      rw [jet_eq_trunc]
      exact sum_trunc_evalXU_rowGroups μ D _ _ (colorGroup_disjoint L t)
        (colorGroup_union L t) table A.row (A.theta t) c.R
        (layoutBeta A lift hLift s t) (fun x w => lift (x w)) A.row_degree

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- Unit differences of lifted nodes follow from residue separation and the
principal nilpotent kernel; they are not an extra interpolation hypothesis. -/
theorem theta_unit_differences (A : LayoutSpec.LiftedLayout L R)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ)
    (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R)) :
    Pairwise (fun i j => IsUnit (A.theta i - A.theta j)) := by
  intro i j hij
  apply NilpotentDefect.isUnit_of_residue_ne_zero A.residue
    (fun z => ⟨s.lift z, s.residue_lift z⟩) (p : R) μ hnil
  · intro z hz
    rw [← Ideal.mem_span_singleton, ← hker]
    exact hz
  · rw [map_sub, A.residue_theta, A.residue_theta]
    intro h
    exact hij (L.node_injective (sub_eq_zero.mp h))

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The concrete finite-sum CRT reconstruction fed by the actual separated
jet computation. The supplied polynomials are algebraic Bezout certificates. -/
def reconstructLayout (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (u : Fin c.Q → Polynomial R) : Polynomial R :=
  JetCRT.reconstructJetsWithBezout A.theta D u (layoutJet A lift hLift s table μ D)

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- CRT recovers H from the defined separated jets. The degree hypothesis is
a polynomial degree condition, discharged below for interpolated factors. -/
theorem reconstructLayout_eq (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (u v : Fin c.Q → Polynomial R)
    (hbez : ∀ t, u t * JetCRT.cofactor A.theta D t +
      v t * JetCRT.nodePower (A.theta t) D = 1)
    (hdegree : (GlobalPolynomial.rowGlobalPolynomial table A.row lift).natDegree < c.Q * D) :
    reconstructLayout A lift hLift s table μ D u =
      GlobalPolynomial.rowGlobalPolynomial table A.row lift := by
  nontriviality R
  apply JetCRT.reconstructJetsWithBezout_eq A.theta D
    (theta_unit_differences A s μ hnil hker) u v _ hbez
  · apply Polynomial.degree_le_natDegree.trans_lt
    exact WithBot.coe_lt_coe.mpr (by simpa using hdegree)
  · intro t
    rw [layoutJet_eq A lift hLift s table μ D hnil hker t]
    exact (TruncatedInverse.jet_modByMonic _ _ _).symm

/-- Each inverse of a node difference is computed by lifting its residue-field
inverse and applying a finite nilpotent geometric correction. -/
def differenceInverse (A : LayoutSpec.LiftedLayout L R)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ)
    (i j : Fin c.Q) : R :=
  NilpotentDefect.residueInverse A.residue s.lift μ (A.theta i - A.theta j)

omit [DecidableEq F] [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem differenceInverse_mul (A : LayoutSpec.LiftedLayout L R)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ)
    (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (i j : Fin c.Q) (hij : i ≠ j) :
    differenceInverse A s μ i j * (A.theta i - A.theta j) = 1 := by
  rw [mul_comm]
  apply NilpotentDefect.mul_residueInverse A.residue s.lift s.residue_lift (p : R) μ hnil
  · intro z hz
    rw [← Ideal.mem_span_singleton, ← hker]
    exact hz
  · rw [map_sub, A.residue_theta, A.residue_theta]
    intro h
    exact hij (L.node_injective (sub_eq_zero.mp h))

/-- Explicit finite geometric CRT reconstruction of the separated jets.
There are no supplied Bezout polynomials or inverse certificates. -/
def explicitReconstruction (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) : Polynomial R :=
  TruncatedInverse.reconstruct A.theta D
    (TruncatedInverse.constantInverse D (differenceInverse A s μ))
    (layoutJet A lift hLift s table μ D)

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem explicitReconstruction_eq (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (s : CosetInvariance.ResidueSection A.residue)
    (table : ∀ e, MvPolynomial {v // v ∈ P.scope e} R)
    (μ D : ℕ) (hD : 0 < D) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hdegree : (GlobalPolynomial.rowGlobalPolynomial table A.row lift).natDegree < c.Q * D) :
    explicitReconstruction A lift hLift s table μ D =
      GlobalPolynomial.rowGlobalPolynomial table A.row lift := by
  nontriviality R
  let _ : Nonempty (Fin c.Q) := ⟨⟨0, c.Q_pos⟩⟩
  apply TruncatedInverse.reconstruct_eq A.theta D hD
    (theta_unit_differences A s μ hnil hker)
  · exact TruncatedInverse.constantInverse_correct A.theta D _
      (differenceInverse_mul A s μ hnil hker)
  · simpa using hdegree
  · intro t
    rw [layoutJet_eq A lift hLift s table μ D hnil hker t, jet_eq_trunc]
    exact TruncatedInverse.trunc_idempotent D _

end LayoutCounting

section InterpolatedCounting

variable {p k Δ : ℕ} [Fact p.Prime]
  {V F K R : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [CommRing R] (S : Factor.System V F (ZMod p)) {c : LayoutSpec.Constants p k Δ}
  {L : LayoutSpec.Layout (E := K) S.toPattern c}

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
omit [DecidableEq F] in
/-- The strict interpolation degree budget follows from the actual bounded
factor pattern and the individual degrees of the explicit table interpolants. -/
theorem interpolated_degree_lt (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R) (hu : TableInterpolation.UnitDifferences lift)
    (hD : 0 < Fintype.card V) :
    (GlobalPolynomial.interpolatedGlobalPolynomial S lift hu A.row).natDegree <
      c.Q * Fintype.card V := by
  have hm : Fintype.card F ≤ Δ * Fintype.card V := by
    apply Incidence.card_factors_le S.scope Δ L.bounded.nonempty_scope
    intro w
    exact L.bounded.incidence_le w
  have hd := GlobalPolynomial.natDegree_interpolatedGlobalPolynomial_le S lift hu A.row
    k c.R L.bounded.arity_le A.row_degree
  calc
    (GlobalPolynomial.interpolatedGlobalPolynomial S lift hu A.row).natDegree ≤
        Fintype.card F * k * (p - 1) * c.R := by simpa only [ZMod.card] using hd
    _ ≤ (Δ * Fintype.card V) * k * (p - 1) * c.R :=
      Nat.mul_le_mul_right c.R (Nat.mul_le_mul_right (p - 1) (Nat.mul_le_mul_right k hm))
    _ = Fintype.card V * (Δ * k * (p - 1) * c.R) := by ac_rfl
    _ < Fintype.card V * c.Q := Nat.mul_lt_mul_of_pos_left c.degree_budget hD
    _ = c.Q * Fintype.card V := Nat.mul_comm _ _

omit [DecidableEq F] in
/-- The actual count value produced by separated jets and explicit CRT. -/
def recoveredValue (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (hu : TableInterpolation.UnitDifferences lift)
    (s : CosetInvariance.ResidueSection A.residue)
    (μ : ℕ) (u : Fin c.Q → Polynomial R) : R :=
  (reconstructLayout A lift hLift s (GlobalPolynomial.interpolatedTable S lift hu)
    μ (Fintype.card V) u).eval 0

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
/-- The layout-to-counting correctness theorem. Every local jet is the
  separated construction above; the target equality is a conclusion. -/
theorem recoveredValue_eq_count (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (hu : TableInterpolation.UnitDifferences lift)
    (s : CosetInvariance.ResidueSection A.residue)
    (μ : ℕ) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hD : 0 < Fintype.card V) (u v : Fin c.Q → Polynomial R)
    (hbez : ∀ t, u t * JetCRT.cofactor A.theta (Fintype.card V) t +
      v t * JetCRT.nodePower (A.theta t) (Fintype.card V) = 1) :
    recoveredValue S A lift hLift hu s μ u = (Factor.count S : R) := by
  unfold recoveredValue
  rw [reconstructLayout_eq A lift hLift s _ μ (Fintype.card V) hnil hker u v hbez
    (interpolated_degree_lt S A lift hu hD)]
  exact GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial S lift hu A.row A.row_zero

/-- The same count computation using finite geometric CRT throughout. -/
def explicitRecoveredValue (A : LayoutSpec.LiftedLayout L R) (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (hu : TableInterpolation.UnitDifferences lift)
    (s : CosetInvariance.ResidueSection A.residue) (μ : ℕ) : R :=
  (explicitReconstruction A lift hLift s (GlobalPolynomial.interpolatedTable S lift hu)
    μ (Fintype.card V)).eval 0

omit [Fintype K] [FiniteDimensional (ZMod p) K] in
theorem explicitRecoveredValue_eq_count (A : LayoutSpec.LiftedLayout L R)
    (lift : ZMod p → R)
    (hLift : ∀ z, A.residue (lift z) = algebraMap (ZMod p) K z)
    (hu : TableInterpolation.UnitDifferences lift)
    (s : CosetInvariance.ResidueSection A.residue)
    (μ : ℕ) (hnil : (p : R) ^ μ = 0)
    (hker : RingHom.ker A.residue = Ideal.span ({(p : R)} : Set R))
    (hD : 0 < Fintype.card V) :
    explicitRecoveredValue S A lift hLift hu s μ = (Factor.count S : R) := by
  unfold explicitRecoveredValue
  rw [explicitReconstruction_eq A lift hLift s _ μ (Fintype.card V) hD hnil hker
    (interpolated_degree_lt S A lift hu hD)]
  exact GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial S lift hu A.row A.row_zero

omit [DecidableEq F] in
/-- The chosen prime-power modulus strictly exceeds every possible count. -/
theorem factor_count_lt_prime_power : Factor.count S < p ^ (Fintype.card V + 1) := by
  calc
    Factor.count S ≤ p ^ Fintype.card V := by
      simpa only [ZMod.card] using Factor.count_le_pow S
    _ < p ^ (Fintype.card V + 1) :=
      Nat.pow_lt_pow_right (Fact.out : Nat.Prime p).one_lt (Nat.lt_succ_self _)

end InterpolatedCounting

section ActualCounting

variable {p k Δ : ℕ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : LayoutSpec.Constants p k Δ}
  (L : LayoutSpec.Layout (E := FiniteField.E p c.h) S.toPattern c)

/-- The completely instantiated ring-valued output: the actual monic-lift
quotient, integer representatives, lifted layout, residue section, separated
moments, and finite geometric CRT are all constructed. -/
def actualRingValue : ActualLiftRing.Ring p c.h (Fintype.card V + 1) :=
  explicitRecoveredValue S
    (ActualLiftRing.liftedLayout L (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift p c.h (Fintype.card V + 1))
    (ActualLiftRing.rho_coordinateLift p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift_unitDifferences p c.h (Fintype.card V + 1))
    (ActualLiftRing.residueSection p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (Fintype.card V + 1)

/-- Every algebraic side condition is discharged for the actual prime-power
ring. Only the supplied layout and nonempty coordinate domain are required. -/
theorem actualRingValue_eq_count (hD : 0 < Fintype.card V) :
    actualRingValue S L =
      (Factor.count S : ActualLiftRing.Ring p c.h (Fintype.card V + 1)) := by
  unfold actualRingValue
  exact explicitRecoveredValue_eq_count S
    (ActualLiftRing.liftedLayout L (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift p c.h (Fintype.card V + 1))
    (ActualLiftRing.rho_coordinateLift p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (ActualLiftRing.coordinateLift_unitDifferences p c.h (Fintype.card V + 1))
    (ActualLiftRing.residueSection p c.h (Fintype.card V + 1) (Nat.succ_pos _))
    (Fintype.card V + 1)
    (ActualLiftRing.prime_power_zero p c.h (Fintype.card V + 1))
    (ActualLiftRing.rho_ker p c.h (Fintype.card V + 1) (Nat.succ_pos _)) hD

/-- Decode the actual ring output as a natural number using its canonical
constant coefficient. This definition does not call the target factor count. -/
def actualCount : ℕ :=
  ActualLiftRing.decodeCount p c.h (Fintype.card V + 1) (Nat.succ_pos _)
    (actualRingValue S L)

/-- Exact natural-number counting from an interpolation layout. The count is
recovered, not merely tested modulo p or compared for zero. No ring, lift,
coefficient, inverse, or desired-result equality is a hypothesis. -/
theorem actualCount_eq_count (hD : 0 < Fintype.card V) :
    actualCount S L = Factor.count S := by
  rw [actualCount, actualRingValue_eq_count S L hD]
  exact ActualLiftRing.decodeCount_natCast p c.h (Fintype.card V + 1) (Nat.succ_pos _)
    (Nat.ne_of_gt c.h_pos) (Factor.count S) (factor_count_lt_prime_power S)

/-- The resulting decision test has exactly the intended satisfying-assignment
semantics. Complexity and a concrete machine realization are separate. -/
theorem actualCount_pos_iff (hD : 0 < Fintype.card V) :
    0 < actualCount S L ↔ ∃ x : V → ZMod p, Factor.Satisfies S x := by
  rw [actualCount_eq_count S L hD]
  exact Factor.count_pos_iff S

end ActualCounting






end

end SubexponentialSAT.Counting

end OAI.Algorithms
