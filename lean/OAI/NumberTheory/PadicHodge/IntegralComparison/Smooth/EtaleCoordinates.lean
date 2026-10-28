import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Etale Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.EtaleCoordinates

noncomputable section

/-!
# IntegralComparison: smooth algebras have finite principal covers by actual étale coordinate charts
-/

universe u

variable (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]

def HasCoordinates (s : C) : Prop :=
  ∃ (σ : Type u) (_ : Fintype σ) (a : Algebra (MvPolynomial σ R) (Localization.Away s)),
    letI := a
    IsScalarTower R (MvPolynomial σ R) (Localization.Away s) ∧
      Algebra.Etale (MvPolynomial σ R) (Localization.Away s)

variable [Algebra.Smooth R C]

theorem exists_at_prime (q : Ideal C) [q.IsPrime] : ∃ s ∉ q, HasCoordinates R C s := by
  obtain ⟨s, hs, n, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away s) := a
  let : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away s) := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away s) := he
  let σ := ULift.{u} (Fin n)
  let e : Fin n ≃ σ := Equiv.ulift.symm
  refine ⟨s, hs, σ, inferInstance, IntegralComparison.Etale.CoordinateReindex.algebra R (Localization.Away s) (Fin n) σ e, ?_⟩
  exact ⟨IntegralComparison.Etale.CoordinateReindex.scalarTower R (Localization.Away s) (Fin n) σ e,
    IntegralComparison.Etale.CoordinateReindex.etale R (Localization.Away s) (Fin n) σ e⟩

theorem exists_finite_cover : ∃ s : Finset C,
    (∀ r ∈ s, HasCoordinates R C r) ∧ Ideal.span (s : Set C) = ⊤ := by
  apply Principal.OpenCover.finite_unit_family
  intro q
  obtain ⟨r, hr, hcoord⟩ := exists_at_prime R C q.asIdeal
  exact ⟨r, hcoord, hr⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.EtaleCoordinates
