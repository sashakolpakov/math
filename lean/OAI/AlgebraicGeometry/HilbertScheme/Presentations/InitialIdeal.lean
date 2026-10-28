import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedMonomialIdeals
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.LinearAlgebra.Projection

/-! # Initial Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.InitialIdeal.GradedHilbert

noncomputable section

/-!
Initial ideals and graded quotient dimensions. Division is applied to
the actual nonzero elements of an ideal. Taking homogeneous components
then gives degree-preserving remainder representatives.
-/

open _root_.MvPolynomial _root_.Module

universe u

variable {K : Type u} [Field K] {n : ℕ}

def initialIdeal (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  Ideal.span ((fun a => monomial a (1 : K)) ''
    (m.degree '' {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n | f ∈ I ∧ f ≠ 0}))

theorem initialIdeal_isMonomial (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : SaturatedMonomialIdeals.GradedHilbert.IsMonomial (initialIdeal m I) := ⟨_, rfl⟩

theorem monomial_mem_initialIdeal_iff (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (a : Fin (n + 1) →₀ ℕ) :
    monomial a (1 : K) ∈ initialIdeal m I ↔
      ∃ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, f ∈ I ∧ f ≠ 0 ∧ m.degree f ≤ a := by
  classical
  simp only [initialIdeal, mem_ideal_span_monomial_image, support_monomial,
    one_ne_zero, ↓reduceIte, Finset.mem_singleton, forall_eq, Set.mem_image,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, ⟨f, hf, rfl⟩, hba⟩
    exact ⟨f, hf.1, hf.2, hba⟩
  · rintro ⟨f, hf, hf0, hfa⟩
    exact ⟨m.degree f, ⟨f, ⟨hf, hf0⟩, rfl⟩, hfa⟩

theorem leading_monomial_mem_initialIdeal (m : MonomialOrder (Fin (n + 1)))
    {I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)} {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} (hf : f ∈ I) (hf0 : f ≠ 0) :
    monomial (m.degree f) (1 : K) ∈ initialIdeal m I :=
  (monomial_mem_initialIdeal_iff m I _).mpr ⟨f, hf, hf0, le_rfl⟩

def standardSpace (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : Submodule K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  restrictSupport K {a | monomial a (1 : K) ∉ initialIdeal m I}

theorem standardSpace_disjoint (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : Disjoint (I.restrictScalars K) (standardSpace m I) := by
  apply Submodule.disjoint_def.mpr
  intro f hf hs
  by_contra hf0
  exact hs (m.degree_mem_support hf0) (leading_monomial_mem_initialIdeal m hf hf0)

theorem exists_standard_remainder (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    ∃ r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, r ∈ standardSpace m I ∧ f - r ∈ I := by
  classical
  let B := {b : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n | b ∈ I ∧ b ≠ 0}
  obtain ⟨g, r, hfr, _, hr⟩ := m.div_set (B := B)
    (fun b hb => m.isUnit_leadingCoeff.mpr hb.2) f
  refine ⟨r, ?_, ?_⟩
  · intro a ha hma
    obtain ⟨b, hb, hb0, hba⟩ := (monomial_mem_initialIdeal_iff m I a).mp hma
    exact hr a ha b ⟨hb, hb0⟩ hba
  · rw [hfr, add_sub_cancel_right]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact I.sum_mem fun b _ => I.mul_mem_left (g b) b.property.1

theorem initialIdeal_eq_self_of_isMonomial (m : MonomialOrder (Fin (n + 1)))
    {I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)} (hI : SaturatedMonomialIdeals.GradedHilbert.IsMonomial I) : initialIdeal m I = I := by
  classical
  apply le_antisymm
  · apply (initialIdeal_isMonomial m I).le_of_monomialExponents_subset
    intro a ha
    obtain ⟨f, hf, hf0, hfa⟩ := (monomial_mem_initialIdeal_iff m I _).mp ha
    have hlead := (hI.mem_iff_support f).mp hf (m.degree f) (m.degree_mem_support hf0)
    have hupper := SaturatedMonomialIdeals.GradedHilbert.monomialExponents_isUpperSet I
    have hmem : Finsupp.equivFunOnFinite (m.degree f) ∈ SaturatedMonomialIdeals.GradedHilbert.monomialExponents I := by
      simpa only [SaturatedMonomialIdeals.GradedHilbert.monomialExponents, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hlead
    exact hupper hfa hmem
  · apply hI.le_of_monomialExponents_subset
    intro a ha
    apply (monomial_mem_initialIdeal_iff m I _).mpr
    refine ⟨monomial (Finsupp.equivFunOnFinite.symm a) (1 : K), ha, ?_, ?_⟩
    · simp only [ne_eq, monomial_eq_zero, one_ne_zero, not_false_eq_true]
    · change m.degree (monomial (Finsupp.equivFunOnFinite.symm a) (1 : K)) ≤
        Finsupp.equivFunOnFinite.symm a
      rw [m.degree_monomial]
      simp

def standardDegreeSpace (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (d : ℕ) : Submodule K (Hilbert.Polynomial.GradedHilbert.grading K n d) :=
  (standardSpace m I).comap (Hilbert.Polynomial.GradedHilbert.grading K n d).subtype

theorem standardDegreeSpace_isCompl (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    IsCompl (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d) (standardDegreeSpace m I.toIdeal d) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro f hf hs
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp (standardSpace_disjoint m I.toIdeal)) f.val hf hs
  · apply codisjoint_iff.mpr
    apply eq_top_iff.mpr
    intro f _
    obtain ⟨r, hr, hfr⟩ := exists_standard_remainder m I.toIdeal f.val
    let s : Hilbert.Polynomial.GradedHilbert.grading K n d := ⟨homogeneousComponent d r, homogeneousComponent_mem d r⟩
    have hs : s ∈ standardDegreeSpace m I.toIdeal d := by
      intro a ha
      have ha' : a ∈ r.support := by
        change a ∈ (homogeneousComponent d r).support at ha
        rw [support_homogeneousComponent] at ha
        exact (Finset.mem_filter.mp ha).1
      exact hr ha'
    apply Submodule.mem_sup.mpr
    refine ⟨f - s, ?_, s, hs, sub_add_cancel f s⟩
    have hcomp := homogeneousComponent_mem_of_mem I.isHomogeneous hfr d
    rw [map_sub, homogeneousComponent_eq_self f.property] at hcomp
    exact hcomp

/-- The quotient in each degree has the standard-monomial complement as
its actual space of representatives. -/
def degreeQuotientEquivStandard (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[K] standardDegreeSpace m I.toIdeal d :=
  Submodule.quotientEquivOfIsCompl _ _ (standardDegreeSpace_isCompl m I d)

def initialHomogeneousIdeal (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) :=
  ⟨initialIdeal m I, (initialIdeal_isMonomial m I).isHomogeneous⟩

/-- Passing to the initial ideal preserves the entire Hilbert function. -/
theorem hilbertFunction_initialIdeal (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (initialIdeal m I.toIdeal) d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  have hinit := initialIdeal_eq_self_of_isMonomial m (initialIdeal_isMonomial m I.toIdeal)
  have heq : standardDegreeSpace m (initialIdeal m I.toIdeal) d =
      standardDegreeSpace m I.toIdeal d := by
    unfold standardDegreeSpace standardSpace
    rw [hinit]
  exact ((degreeQuotientEquivStandard m (initialHomogeneousIdeal m I.toIdeal) d).trans
    ((LinearEquiv.ofEq _ _ heq).trans (degreeQuotientEquivStandard m I d).symm)).finrank_eq

theorem hasHilbertPolynomial_initialIdeal_iff (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (initialIdeal m I.toIdeal) P ↔ Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  simp only [Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, hilbertFunction_initialIdeal]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.InitialIdeal.GradedHilbert
