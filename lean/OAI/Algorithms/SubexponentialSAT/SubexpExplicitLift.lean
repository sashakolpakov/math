import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing

namespace OAI.Algorithms

/-!
# Explicit finite coefficient lifts of a multicolor layout

The polynomial lift uses exactly `bound + 1` coefficients of the original
polynomial and applies one fixed residue section to each. No polynomial or
node is obtained by choosing an arbitrary preimage of a surjective map.
The section is an ordinary function, not a ring homomorphism.
-/

namespace SubexponentialSAT.SubexpExplicitLift

open scoped BigOperators

section Coefficients

variable {E Λ : Type*} [CommSemiring E] [CommSemiring Λ]

/-- The explicit array of lifted coefficients, including zero padding up to
the supplied degree bound. -/
def coefficientData (sectionValue : E → Λ) (bound : ℕ) (f : Polynomial E) :
    Fin (bound + 1) → Λ :=
  fun i => sectionValue (f.coeff i.val)

/-- Reconstruct the lift from the finite list of source coefficients. -/
noncomputable def liftPolynomial (sectionValue : E → Λ) (bound : ℕ)
    (f : Polynomial E) : Polynomial Λ :=
  ∑ n ∈ Finset.range (bound + 1), Polynomial.monomial n (sectionValue (f.coeff n))

/-- The construction is literally a finite array fold over `bound + 1`
entries. This identity makes the data inspected by the lift explicit. -/
theorem liftPolynomial_eq_coefficientData (sectionValue : E → Λ) (bound : ℕ)
    (f : Polynomial E) :
    liftPolynomial sectionValue bound f =
      ∑ i : Fin (bound + 1), Polynomial.monomial i.val
        (coefficientData sectionValue bound f i) := by
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun n => Polynomial.monomial n (sectionValue (f.coeff n))) (bound + 1)

@[simp]
theorem coeff_liftPolynomial (sectionValue : E → Λ) (bound : ℕ)
    (f : Polynomial E) (n : ℕ) :
    (liftPolynomial sectionValue bound f).coeff n =
      if n ≤ bound then sectionValue (f.coeff n) else 0 := by
  simp [liftPolynomial, Polynomial.coeff_monomial
    ]

/-- With a zero-preserving section and a valid bound, every coefficient is
exactly the image of the corresponding original coefficient. -/
theorem coeff_liftPolynomial_of_degree_le (sectionValue : E → Λ)
    (section_zero : sectionValue 0 = 0) (bound : ℕ) (f : Polynomial E)
    (hdegree : f.natDegree ≤ bound) (n : ℕ) :
    (liftPolynomial sectionValue bound f).coeff n = sectionValue (f.coeff n) := by
  rw [coeff_liftPolynomial]
  by_cases hn : n ≤ bound
  · simp only [hn, ↓reduceIte]
  · rw [ite_eq_right hn, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdegree (Nat.lt_of_not_ge hn)), section_zero]

/-- Finite reconstruction cannot introduce a coefficient beyond the stated
bound, irrespective of any algebraic property of the section. -/
theorem natDegree_liftPolynomial_le_bound (sectionValue : E → Λ)
    (bound : ℕ) (f : Polynomial E) :
    (liftPolynomial sectionValue bound f).natDegree ≤ bound := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [coeff_liftPolynomial, ite_eq_right (Nat.not_le.mpr hn)]

/-- Zero preservation also prevents the padding from increasing the degree
above that of the source polynomial. -/
theorem natDegree_liftPolynomial_le (sectionValue : E → Λ)
    (section_zero : sectionValue 0 = 0) (bound : ℕ) (f : Polynomial E)
    (hdegree : f.natDegree ≤ bound) :
    (liftPolynomial sectionValue bound f).natDegree ≤ f.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_liftPolynomial_of_degree_le sectionValue section_zero bound f hdegree,
    Polynomial.coeff_eq_zero_of_natDegree_lt hn, section_zero]

/-- Reduction recovers the original polynomial coefficient by coefficient. -/
theorem map_liftPolynomial (ρ : Λ →+* E) (sectionValue : E → Λ)
    (section_zero : sectionValue 0 = 0)
    (residue_section : ∀ z, ρ (sectionValue z) = z)
    (bound : ℕ) (f : Polynomial E) (hdegree : f.natDegree ≤ bound) :
    (liftPolynomial sectionValue bound f).map ρ = f := by
  ext n
  rw [Polynomial.coeff_map,
    coeff_liftPolynomial_of_degree_le sectionValue section_zero bound f hdegree,
    residue_section]

/-- The lift preserves the source degree exactly when it has a residue
left inverse. In particular the layout degree budget is unchanged. -/
theorem natDegree_liftPolynomial_eq (ρ : Λ →+* E) (sectionValue : E → Λ)
    (section_zero : sectionValue 0 = 0)
    (residue_section : ∀ z, ρ (sectionValue z) = z)
    (bound : ℕ) (f : Polynomial E) (hdegree : f.natDegree ≤ bound) :
    (liftPolynomial sectionValue bound f).natDegree = f.natDegree := by
  apply le_antisymm (natDegree_liftPolynomial_le sectionValue section_zero bound f hdegree)
  have h := Polynomial.natDegree_map_le
    (p := liftPolynomial sectionValue bound f) (f := ρ)
  rwa [map_liftPolynomial ρ sectionValue section_zero residue_section bound f hdegree] at h

@[simp]
theorem eval_zero_liftPolynomial (sectionValue : E → Λ)
    (bound : ℕ) (f : Polynomial E) :
    (liftPolynomial sectionValue bound f).eval 0 = sectionValue (f.eval 0) := by
  simp only [← Polynomial.coeff_zero_eq_eval_zero, coeff_liftPolynomial,
    Nat.zero_le, ↓reduceIte]

end Coefficients

section Layout

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F E Λ : Type*} [Fintype V] [DecidableEq V] [Fintype F]
  [Field E] [Algebra (ZMod p) E] [CommRing Λ]
  {P : Factor.Pattern V F} {c : SubexpLayoutSpec.Parameters p k Δ r tau}

/-- Lift every node and every one of the `c.R + 1` row coefficients through
the given fixed section. Preserving zero and one gives the exact coordinate
row at the origin, rather than only its residue. -/
noncomputable def fromSection (L : SubexpLayoutSpec.Layout (E := E) P c)
    (ρ : Λ →+* E) (sectionValue : E → Λ)
    (section_zero : sectionValue 0 = 0) (section_one : sectionValue 1 = 1)
    (residue_section : ∀ z, ρ (sectionValue z) = z) :
    SubexpLayoutSpec.LiftedLayout L Λ where
  residue := ρ
  theta t := sectionValue (L.node t)
  residue_theta t := residue_section (L.node t)
  row e v w := liftPolynomial sectionValue c.R (L.row e v w)
  residue_row e v w :=
    map_liftPolynomial ρ sectionValue section_zero residue_section c.R
      (L.row e v w) (L.row_degree e v w)
  row_zero e v w := by
    rw [eval_zero_liftPolynomial, L.row_zero]
    split_ifs <;> assumption
  row_degree e v w := natDegree_liftPolynomial_le_bound sectionValue c.R (L.row e v w)

@[simp]
theorem fromSection_residue (L : SubexpLayoutSpec.Layout (E := E) P c)
    (ρ : Λ →+* E) (sectionValue : E → Λ)
    (h0 : sectionValue 0 = 0) (h1 : sectionValue 1 = 1)
    (hs : ∀ z, ρ (sectionValue z) = z) :
    (fromSection L ρ sectionValue h0 h1 hs).residue = ρ := rfl

@[simp]
theorem fromSection_theta (L : SubexpLayoutSpec.Layout (E := E) P c)
    (ρ : Λ →+* E) (sectionValue : E → Λ)
    (h0 : sectionValue 0 = 0) (h1 : sectionValue 1 = 1)
    (hs : ∀ z, ρ (sectionValue z) = z) (t : Fin c.Q) :
    (fromSection L ρ sectionValue h0 h1 hs).theta t = sectionValue (L.node t) := rfl

/-- Every stored row coefficient has the promised explicit formula. -/
theorem fromSection_row_coeff (L : SubexpLayoutSpec.Layout (E := E) P c)
    (ρ : Λ →+* E) (sectionValue : E → Λ)
    (h0 : sectionValue 0 = 0) (h1 : sectionValue 1 = 1)
    (hs : ∀ z, ρ (sectionValue z) = z)
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) (n : ℕ) :
    ((fromSection L ρ sectionValue h0 h1 hs).row e v w).coeff n =
      sectionValue ((L.row e v w).coeff n) :=
  coeff_liftPolynomial_of_degree_le sectionValue h0 c.R
    (L.row e v w) (L.row_degree e v w) n

end Layout

section SelectedRing

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F]
  {P : Factor.Pattern V F} {c : SubexpLayoutSpec.Parameters p k Δ r tau}

/-- The selected-ring lift of an actual multicolor layout. Nodes and all row
coefficients use the explicit four-coordinate residue section. This does
not invoke the generic surjective-preimage layout construction. -/
noncomputable def explicitLiftedLayout
    (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) P c)
    (μ : ℕ) (hμ : 0 < μ) :
    SubexpLayoutSpec.LiftedLayout L (SubexpActualRing.Ring p μ) :=
  fromSection L (SubexpActualRing.rho p μ hμ)
    (SubexpActualRing.sectionValue p μ hμ)
    (SubexpActualRing.sectionValue_zero p μ hμ)
    (SubexpActualRing.sectionValue_one p μ hμ)
    (SubexpActualRing.rho_sectionValue p μ hμ)

@[simp]
theorem explicitLiftedLayout_residue
    (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) P c)
    (μ : ℕ) (hμ : 0 < μ) :
    (explicitLiftedLayout L μ hμ).residue = SubexpActualRing.rho p μ hμ := rfl

@[simp]
theorem explicitLiftedLayout_theta
    (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) P c)
    (μ : ℕ) (hμ : 0 < μ) (t : Fin c.Q) :
    (explicitLiftedLayout L μ hμ).theta t =
      SubexpActualRing.sectionValue p μ hμ (L.node t) := rfl

/-- The exact source-to-target coefficient rule for every lifted incidence. -/
theorem explicitLiftedLayout_row_coeff
    (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) P c)
    (μ : ℕ) (hμ : 0 < μ)
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) (n : ℕ) :
    ((explicitLiftedLayout L μ hμ).row e v w).coeff n =
      SubexpActualRing.sectionValue p μ hμ ((L.row e v w).coeff n) :=
  fromSection_row_coeff L (SubexpActualRing.rho p μ hμ)
    (SubexpActualRing.sectionValue p μ hμ)
    (SubexpActualRing.sectionValue_zero p μ hμ)
    (SubexpActualRing.sectionValue_one p μ hμ)
    (SubexpActualRing.rho_sectionValue p μ hμ) e v w n

/-- The semantic row is constructed from precisely `c.R + 1` explicitly
lifted coefficient entries, including zero padding. -/
theorem explicitLiftedLayout_row_eq_sum
    (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) P c)
    (μ : ℕ) (hμ : 0 < μ)
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) :
    (explicitLiftedLayout L μ hμ).row e v w =
      ∑ i : Fin (c.R + 1), Polynomial.monomial i.val
        (SubexpActualRing.sectionValue p μ hμ ((L.row e v w).coeff i.val)) :=
  liftPolynomial_eq_coefficientData (SubexpActualRing.sectionValue p μ hμ)
    c.R (L.row e v w)

/-- The lift changes no incidence-polynomial degree. -/
theorem explicitLiftedLayout_row_natDegree
    (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) P c)
    (μ : ℕ) (hμ : 0 < μ)
    (e : F) (v : {v // v ∈ P.scope e}) (w : V) :
    ((explicitLiftedLayout L μ hμ).row e v w).natDegree =
      (L.row e v w).natDegree :=
  natDegree_liftPolynomial_eq (SubexpActualRing.rho p μ hμ)
    (SubexpActualRing.sectionValue p μ hμ)
    (SubexpActualRing.sectionValue_zero p μ hμ)
    (SubexpActualRing.rho_sectionValue p μ hμ)
    c.R (L.row e v w) (L.row_degree e v w)

end SelectedRing

end SubexponentialSAT.SubexpExplicitLift

end OAI.Algorithms
