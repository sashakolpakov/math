import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSeparation

namespace OAI.Algorithms

/-!
# Family moments for an arbitrary number of color groups

This module connects the dependent-fiber separation theorem to actual
multivariate coefficient extraction and to the nested U/Z/X representation.
The Pi sum is used only as a semantic identity; the separated expressions
contain one inner sum per group and no Cartesian-product enumeration.

The list interfaces accept a verified, duplicate-free exponent enumeration.
They make no assumption about how that enumeration was produced and make no
runtime claim.  Canonical clipping of a product is handled separately by the
counting and truncation modules.
-/

namespace SubexponentialSAT.SubexpMoments

noncomputable section

open scoped BigOperators

section FamilySum

variable {R S Ω O G : Type*} {X : O → G → Type*}
  [CommSemiring R] [CommSemiring S]
  [Fintype Ω] [Fintype O] [Fintype G] [DecidableEq G]
  [∀ o g, Fintype (X o g)]

/-- The separated r-fold sum, with scalar weights mapped to the value ring. -/
def familySum (φ : R →+* S) (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (A : G → Ω → S)
    (c : O → R) (wg : ∀ o g, X o g → R) : S :=
  ∑ o, φ (c o) * ∏ g, ∑ y : X o g,
    φ (wg o g y) * A g (e.symm ⟨o, Function.update (reps o) g y⟩)

/-- The definition is the full weighted family moment whenever each group
depends only on its own coordinate and the scalar weight factors. -/
theorem familySum_eq (φ : R →+* S) (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (A : G → Ω → S) (w : Ω → R)
    (c : O → R) (wg : ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ o x, w (e.symm ⟨o, x⟩) = c o * ∏ g, wg o g (x g)) :
    familySum φ e reps A c wg = ∑ z, φ (w z) * ∏ g, A g z := by
  exact (SubexpSeparation.weighted_separation_equiv_map_weights
    φ e reps A w c wg hA hw).symm

end FamilySum

section PolynomialMoments

variable {ι R Ω O G : Type*} {X : O → G → Type*}
  [CommSemiring R] [Fintype Ω] [Fintype O] [Fintype G] [DecidableEq G]
  [∀ o g, Fintype (X o g)]

/-- Actual multivariate polynomial-valued family moment, computed by
independent inner sums at each outer datum. -/
def mvFamilyMoment (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (A : G → Ω → MvPolynomial ι R)
    (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R) (a : ι →₀ ℕ) : MvPolynomial ι R :=
  familySum MvPolynomial.C e reps A (c a) (wg a)

theorem mvFamilyMoment_eq (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (A : G → Ω → MvPolynomial ι R)
    (v : Ω → ι → R) (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g)) (a : ι →₀ ℕ) :
    mvFamilyMoment e reps A c wg a =
      Moments.moment Finset.univ (fun z => ∏ g, A g z) v a :=
  familySum_eq MvPolynomial.C e reps A (fun z => Moments.weight a (v z))
    (c a) (wg a) hA (hw a)

/-- Summing actual coefficients of separated family moments restores the
input coordinates in the entire family product. -/
theorem sum_coeff_mvFamilyMoment_eq
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (A : G → Ω → MvPolynomial ι R) (v : Ω → ι → R)
    (M : Finset (ι →₀ ℕ)) (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g))
    (hsupport : ∀ z, (∏ g, A g z).support ⊆ M) :
    (∑ a ∈ M, (mvFamilyMoment e reps A c wg a).coeff a) =
      ∑ z, MvPolynomial.eval (v z) (∏ g, A g z) := by
  simp_rw [mvFamilyMoment_eq e reps A v c wg hA hw]
  exact Moments.sum_coeff_moment_eq_sum_eval Finset.univ M
    (fun z => ∏ g, A g z) v (fun z _ => hsupport z)

/-- The nested U/Z/X family moment used by the symbolic backend. -/
def nestedFamilyMoment (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (A : G → Ω → Truncation.Poly ι R)
    (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R) (a : ι →₀ ℕ) :
    Truncation.Poly ι R :=
  familySum WeightedSupport.scalarHom e reps A (c a) (wg a)

theorem nestedFamilyMoment_eq (e : Ω ≃ Σ o, ∀ g, X o g)
    (reps : ∀ o g, X o g) (A : G → Ω → Truncation.Poly ι R)
    (v : Ω → ι → R) (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g)) (a : ι →₀ ℕ) :
    nestedFamilyMoment e reps A c wg a =
      ∑ z, WeightedSupport.scalarHom (Moments.weight a (v z)) * ∏ g, A g z :=
  by
    unfold nestedFamilyMoment
    apply familySum_eq
    · exact hA
    · exact hw a

/-- Extract X while retaining U and Z, as an additive map on representatives. -/
def extractX (a : ι →₀ ℕ) :
    Truncation.Poly ι R →+ Polynomial (Polynomial R) :=
  Truncation.mapCoeffs (Truncation.mapCoeffs (MvPolynomial.coeffAddMonoidHom a))

/-- Exact nested family-moment restoration.  The support premise concerns
the complete product, not the separate groups.  No clipping or evaluation of
a quotient is hidden in this statement. -/
theorem sum_extract_nestedFamilyMoment_eq
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (A : G → Ω → Truncation.Poly ι R) (v : Ω → ι → R)
    (M : Finset (ι →₀ ℕ)) (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g))
    (hsupport : ∀ z j r, (((∏ g, A g z).coeff j).coeff r).support ⊆ M) :
    (∑ a ∈ M, (extractX a (nestedFamilyMoment e reps A c wg a)).eval 1) =
      ∑ z, Truncation.evalXU (v z) (∏ g, A g z) := by
  simp_rw [nestedFamilyMoment_eq e reps A v c wg hA hw]
  exact Moments.sum_nested_moments_eval_one_eq_sum_evalXU Finset.univ M
    (fun z => ∏ g, A g z) v (fun z _ => hsupport z)

end PolynomialMoments

section ListedMoments

variable {ι R Ω : Type*} [CommSemiring R] [Fintype Ω]

/-- A duplicate-free explicit exponent list is interchangeable with its
finite-set semantics.  Coverage is a support statement, not an assumed
evaluation identity. -/
theorem list_nested_moments_eval_one_eq_sum_evalXU
    (as : List (ι →₀ ℕ)) (hnodup : as.Nodup)
    (A : Ω → Truncation.Poly ι R) (v : Ω → ι → R)
    (hsupport : ∀ z j r a,
      a ∈ (((A z).coeff j).coeff r).support → a ∈ as) :
    (as.map fun a =>
      (extractX a (∑ z, WeightedSupport.scalarHom (Moments.weight a (v z)) * A z)).eval 1).sum =
      ∑ z, Truncation.evalXU (v z) (A z) := by
  classical
  rw [← List.sum_toFinset _ hnodup]
  exact Moments.sum_nested_moments_eval_one_eq_sum_evalXU Finset.univ as.toFinset
    A v (fun z _ j r a ha => List.mem_toFinset.mpr (hsupport z j r a ha))

/-- A verified degree-bounded list supplies coverage without constructing
the full coordinate box used by the denotational `Moments.retained`. -/
theorem list_nested_moments_eval_one_eq_sum_evalXU_of_degree_bound
    (N : ℕ) (as : List (ι →₀ ℕ)) (hnodup : as.Nodup)
    (hcover : ∀ a : ι →₀ ℕ, a.sum (fun _ n => n) ≤ N → a ∈ as)
    (A : Ω → Truncation.Poly ι R) (v : Ω → ι → R)
    (hdegree : ∀ z j r, (((A z).coeff j).coeff r).totalDegree ≤ N) :
    (as.map fun a =>
      (extractX a (∑ z, WeightedSupport.scalarHom (Moments.weight a (v z)) * A z)).eval 1).sum =
      ∑ z, Truncation.evalXU (v z) (A z) := by
  apply list_nested_moments_eval_one_eq_sum_evalXU as hnodup A v
  intro z j r a ha
  exact hcover a ((MvPolynomial.le_totalDegree ha).trans (hdegree z j r))

end ListedMoments

section ListedFamilyMoments

variable {ι R Ω O G : Type*} {X : O → G → Type*}
  [CommSemiring R] [Fintype Ω] [Fintype O] [Fintype G] [DecidableEq G]
  [∀ o g, Fintype (X o g)]

/-- A list-driven moment loop combined with the r-fold separated inner
sums.  All coefficient extraction is performed after constructing each
complete polynomial moment. -/
theorem list_extract_nestedFamilyMoment_eq
    (e : Ω ≃ Σ o, ∀ g, X o g) (reps : ∀ o g, X o g)
    (A : G → Ω → Truncation.Poly ι R) (v : Ω → ι → R)
    (as : List (ι →₀ ℕ)) (hnodup : as.Nodup)
    (c : (ι →₀ ℕ) → O → R)
    (wg : (ι →₀ ℕ) → ∀ o g, X o g → R)
    (hA : ∀ o g x y, x g = y g →
      A g (e.symm ⟨o, x⟩) = A g (e.symm ⟨o, y⟩))
    (hw : ∀ a o x, Moments.weight a (v (e.symm ⟨o, x⟩)) =
      c a o * ∏ g, wg a o g (x g))
    (hsupport : ∀ z j r a,
      a ∈ (((∏ g, A g z).coeff j).coeff r).support → a ∈ as) :
    (as.map fun a => (extractX a (nestedFamilyMoment e reps A c wg a)).eval 1).sum =
      ∑ z, Truncation.evalXU (v z) (∏ g, A g z) := by
  simp_rw [nestedFamilyMoment_eq e reps A v c wg hA hw]
  exact list_nested_moments_eval_one_eq_sum_evalXU as hnodup
    (fun z => ∏ g, A g z) v hsupport

end ListedFamilyMoments

end

end SubexponentialSAT.SubexpMoments

end OAI.Algorithms
