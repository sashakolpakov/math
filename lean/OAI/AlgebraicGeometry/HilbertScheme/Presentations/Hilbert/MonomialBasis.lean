import OAI.AlgebraicGeometry.HilbertScheme.Presentations.InitialIdeal

/-! # Monomial Basis -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis.GradedHilbert

noncomputable section

/-!
The graded quotient dimension is the number of standard monomials of
that degree. In particular, monomial ideals defined by the same exponent
generators have the same Hilbert function over any two fields.
-/

open _root_.MvPolynomial _root_.Module

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

theorem mem_degreeSpace_iff_support (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (d : ℕ) :
    f ∈ Hilbert.Polynomial.GradedHilbert.grading R n d ↔ ∀ a ∈ f.support, a.degree = d := by
  rw [Hilbert.Polynomial.GradedHilbert.grading, homogeneousSubmodule_eq_finsupp_supported]
  rfl

variable {K : Type u} [Field K]

def standardDegreeMonomials (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (d : ℕ) : Set (Fin (n + 1) →₀ ℕ) :=
  {a | a.degree = d ∧ monomial a (1 : K) ∉ InitialIdeal.GradedHilbert.initialIdeal m I}

def standardDegreeSpaceEquivSupported (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (d : ℕ) :
    InitialIdeal.GradedHilbert.standardDegreeSpace m I d ≃ₗ[K] restrictSupport K (standardDegreeMonomials m I d) where
  toFun f := ⟨f.val.val, fun a ha =>
    ⟨(mem_degreeSpace_iff_support f.val.val d).mp f.val.property a ha, f.property ha⟩⟩
  invFun f := ⟨⟨f.val, (mem_degreeSpace_iff_support f.val d).mpr
    (fun _ ha => (f.property ha).1)⟩, fun _ ha => (f.property ha).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def standardDegreeBasis (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Basis (standardDegreeMonomials m I.toIdeal d) K (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
  (basisRestrictSupport K (standardDegreeMonomials m I.toIdeal d)).map
    ((standardDegreeSpaceEquivSupported m I.toIdeal d).symm.trans
      (InitialIdeal.GradedHilbert.degreeQuotientEquivStandard m I d).symm)

theorem hilbertFunction_eq_card_standard (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d = Nat.card (standardDegreeMonomials m I.toIdeal d) :=
  Module.finrank_eq_nat_card_basis (standardDegreeBasis m I d)

def monomialSpan (K : Type u) [Field K] (S : Set (Fin (n + 1) →₀ ℕ)) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) :=
  ⟨Ideal.span ((fun a => monomial a (1 : K)) '' S),
    SaturatedMonomialIdeals.GradedHilbert.IsMonomial.isHomogeneous ⟨S, rfl⟩⟩

theorem hilbertFunction_monomialSpan (S : Set (Fin (n + 1) →₀ ℕ)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (monomialSpan K S).toIdeal d =
      Nat.card {a : Fin (n + 1) →₀ ℕ | a.degree = d ∧ ∀ b ∈ S, ¬ b ≤ a} := by
  classical
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  rw [hilbertFunction_eq_card_standard m]
  have heq : standardDegreeMonomials m (monomialSpan K S).toIdeal d =
      {a : Fin (n + 1) →₀ ℕ | a.degree = d ∧ ∀ b ∈ S, ¬ b ≤ a} := by
    ext a
    simp only [standardDegreeMonomials, Set.mem_ofPred_eq,
      InitialIdeal.GradedHilbert.initialIdeal_eq_self_of_isMonomial m (show SaturatedMonomialIdeals.GradedHilbert.IsMonomial (monomialSpan K S).toIdeal
        from ⟨S, rfl⟩)]
    change (a.degree = d ∧ monomial a (1 : K) ∉
      Ideal.span ((fun b => monomial b (1 : K)) '' S)) ↔ _
    simp only [mem_ideal_span_monomial_image, support_monomial, one_ne_zero,
      ↓reduceIte, Finset.mem_singleton, forall_eq, not_exists, not_and]
  rw [heq]

theorem hilbertFunction_monomialSpan_field_independent
    (L : Type v) [Field L] (S : Set (Fin (n + 1) →₀ ℕ)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (monomialSpan K S).toIdeal d =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (monomialSpan L S).toIdeal d := by
  rw [hilbertFunction_monomialSpan, hilbertFunction_monomialSpan]

theorem hasHilbertPolynomial_monomialSpan_field_independent
    (L : Type v) [Field L] (S : Set (Fin (n + 1) →₀ ℕ)) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (monomialSpan K S).toIdeal P ↔
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (monomialSpan L S).toIdeal P := by
  simp only [Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, hilbertFunction_monomialSpan]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis.GradedHilbert
