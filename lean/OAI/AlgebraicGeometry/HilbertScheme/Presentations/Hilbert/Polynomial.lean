import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert

noncomputable section

/-!
Graded coordinate quotients and the fixed Hilbert-polynomial condition.
The dimensions below are dimensions of actual quotient modules. Saturation
is expressed by the usual homogeneous test using all forms of one degree.
Existence and uniform boundedness of Hilbert polynomials are separate results.
-/

open _root_.Module

universe u

abbrev CoordinateRing (R : Type u) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) R

abbrev grading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (CoordinateRing R n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

instance coordinateGradedAlgebra (R : Type u) [CommRing R] (n : ℕ) :
    GradedAlgebra (grading R n) := MvPolynomial.gradedAlgebra

instance degreeSpace_finite (R : Type u) [CommRing R] (n d : ℕ) :
    Module.Finite R (grading R n d) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin (n + 1)) R d)

variable {R : Type u} [CommRing R] {n : ℕ}

def degreeRelations (I : Ideal (CoordinateRing R n)) (d : ℕ) :
    Submodule R (grading R n d) :=
  (I.restrictScalars R).comap (grading R n d).subtype

abbrev DegreeQuotient (I : Ideal (CoordinateRing R n)) (d : ℕ) :=
  (grading R n d) ⧸ degreeRelations I d

instance degreeQuotient_finite (I : Ideal (CoordinateRing R n)) (d : ℕ) :
    Module.Finite R (DegreeQuotient I d) := inferInstance

theorem degreeRelations_mono {I J : Ideal (CoordinateRing R n)} (h : I ≤ J) (d : ℕ) :
    degreeRelations I d ≤ degreeRelations J d := by
  intro f hf
  exact h hf

def hilbertFunction (I : Ideal (CoordinateRing R n)) (d : ℕ) : ℕ :=
  Module.finrank R (DegreeQuotient I d)

def HasHilbertPolynomial (I : Ideal (CoordinateRing R n)) (P : Polynomial ℚ) : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → (hilbertFunction I d : ℚ) = P.eval (d : ℚ)

theorem hilbertPolynomial_unique {I : Ideal (CoordinateRing R n)}
    {P Q : Polynomial ℚ} (hP : HasHilbertPolynomial I P) (hQ : HasHilbertPolynomial I Q) :
    P = Q := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  let d₀ := max p q
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun m : ℕ => ((d₀ + m : ℕ) : ℚ)) := by
    intro a b h
    change ((d₀ + a : ℕ) : ℚ) = ((d₀ + b : ℕ) : ℚ) at h
    have h' : d₀ + a = d₀ + b := by exact_mod_cast h
    exact Nat.add_left_cancel h'
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨m, rfl⟩
  exact (hp (d₀ + m) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))).symm.trans
    (hq (d₀ + m) (le_trans (le_max_right _ _) (Nat.le_add_right _ _)))

/-- Homogeneous saturation with respect to the irrelevant ideal: a form
whose multiples by all degree-m forms lie in I must itself lie in I. -/
def IsSaturated (I : Ideal (CoordinateRing R n)) : Prop :=
  ∀ (f : CoordinateRing R n) (d : ℕ), f.IsHomogeneous d →
    (∃ m : ℕ, ∀ g : CoordinateRing R n, g.IsHomogeneous m → g * f ∈ I) → f ∈ I

variable {K : Type u} [Field K] {I J : Ideal (CoordinateRing K n)}

theorem degreeRelations_eq_of_le_of_hilbertFunction_eq
    (hIJ : I ≤ J) (d : ℕ) (hd : hilbertFunction I d = hilbertFunction J d) :
    degreeRelations I d = degreeRelations J d := by
  apply Submodule.eq_of_le_of_finrank_eq (degreeRelations_mono hIJ d)
  have hI := (degreeRelations I d).finrank_quotient_add_finrank
  have hJ := (degreeRelations J d).finrank_quotient_add_finrank
  change Module.finrank K (DegreeQuotient I d) =
    Module.finrank K (DegreeQuotient J d) at hd
  dsimp only [DegreeQuotient] at hd
  rw [hd] at hI
  exact Nat.add_left_cancel (hI.trans hJ.symm)

theorem homogeneous_mem_iff_of_le_of_hilbertFunction_eq
    (hIJ : I ≤ J) (d : ℕ) (hd : hilbertFunction I d = hilbertFunction J d)
    (f : CoordinateRing K n) (hf : f.IsHomogeneous d) : f ∈ I ↔ f ∈ J := by
  have heq := degreeRelations_eq_of_le_of_hilbertFunction_eq hIJ d hd
  change (⟨f, hf⟩ : grading K n d) ∈ degreeRelations I d ↔
    (⟨f, hf⟩ : grading K n d) ∈ degreeRelations J d
  rw [heq]

/-- A saturated homogeneous ideal cannot be strictly contained in a
homogeneous ideal with the same eventual Hilbert polynomial. -/
theorem saturated_eq_of_le_same_hilbertPolynomial
    (I J : HomogeneousIdeal (grading K n)) (hIJ : I ≤ J)
    (hSat : IsSaturated I.toIdeal) (P : Polynomial ℚ)
    (hI : HasHilbertPolynomial I.toIdeal P) (hJ : HasHilbertPolynomial J.toIdeal P) :
    I = J := by
  obtain ⟨i₀, hi⟩ := hI
  obtain ⟨j₀, hj⟩ := hJ
  let m := max i₀ j₀
  have hdim (d : ℕ) (hd : m ≤ d) :
      hilbertFunction I.toIdeal d = hilbertFunction J.toIdeal d := by
    have h := (hi d (le_trans (le_max_left _ _) hd)).trans
      (hj d (le_trans (le_max_right _ _) hd)).symm
    exact_mod_cast h
  apply HomogeneousIdeal.ext'
  intro d f hf
  constructor
  · exact fun h => hIJ h
  · intro hfJ
    apply hSat f d hf
    refine ⟨m, fun g hg => ?_⟩
    apply (homogeneous_mem_iff_of_le_of_hilbertFunction_eq
      (I := I.toIdeal) (J := J.toIdeal) hIJ (m + d)
      (hdim (m + d) (Nat.le_add_right _ _)) (g * f) (hg.mul hf)).mpr
    exact J.toIdeal.mul_mem_left g hfJ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert
