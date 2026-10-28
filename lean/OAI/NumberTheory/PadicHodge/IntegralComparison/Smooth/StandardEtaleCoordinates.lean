import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Standard Etale Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.StandardEtaleCoordinates

noncomputable section

/-! Finite principal covers retaining the actual standard etale presentations. -/

universe u

variable (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]

def HasCoordinates (s : C) : Prop :=
  ∃ (n : ℕ) (a : Algebra (MvPolynomial (Fin n) R) (Localization.Away s)),
    letI := a
    IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away s) ∧
      Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away s)

variable [Algebra.Smooth R C]

theorem exists_at_prime (q : Ideal C) [q.IsPrime] : ∃ s ∉ q, HasCoordinates R C s :=
  Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)

theorem exists_finite_cover : ∃ s : Finset C,
    (∀ r ∈ s, HasCoordinates R C r) ∧ Ideal.span (s : Set C) = ⊤ := by
  apply Principal.OpenCover.finite_unit_family
  intro q
  obtain ⟨r, hr, hcoord⟩ := exists_at_prime R C q.asIdeal
  exact ⟨r, hcoord, hr⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.StandardEtaleCoordinates
