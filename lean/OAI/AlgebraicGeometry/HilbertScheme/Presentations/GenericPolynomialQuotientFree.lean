import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegralPolynomialLeadingCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FieldCoverTransfer
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Generic Polynomial Quotient Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericPolynomialQuotientFree.GradedHilbert

noncomputable section

/-! A polynomial quotient over a domain becomes a free module after
inverting one nonzero coefficient. -/

open _root_.MvPolynomial
open scoped BigOperators

universe u
variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

theorem exists_generic_free_polynomial_quotient (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) :
    ∃ s : R, s ≠ 0 ∧ Module.Free (Localization.Away s)
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing (Localization.Away s) n ⧸
        I.map (MvPolynomial.map (algebraMap R (Localization.Away s)))) := by
  classical
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  obtain ⟨B, hB, hcover⟩ := IntegralPolynomialLeadingCover.GradedHilbert.exists_integral_polynomial_leading_cover m I
  let s : R := ∏ b : B, m.leadingCoeff b.val
  have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun b _ => m.leadingCoeff_ne_zero_iff.mpr (hB b.val b.property).2)
  let A := Localization.Away s
  let K := FractionRing R
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hunit : IsUnit (algebraMap R K s) := isUnit_iff_ne_zero.mpr
    (fun h => hs (hRK (h.trans (map_zero _).symm)))
  let g : A →+* K := IsLocalization.Away.lift s hunit
  have hg (r : R) : g (algebraMap R A r) = algebraMap R K r :=
    IsLocalization.Away.lift_eq s hunit r
  have hRA : Function.Injective (algebraMap R A) := by
    intro x y hxy
    apply hRK
    rw [← hg x, ← hg y, hxy]
  have hAK : Function.Injective g := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers s) g).mpr
    intro x y
    rw [hg, hg]
    exact hRA.eq_iff.trans hRK.eq_iff.symm
  let : Algebra A K := g.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq (fun r => (hg r).symm)
  refine ⟨s, hs, ?_⟩
  apply Polynomial.FieldCoverTransfer.polynomial_quotient_free_of_field_cover A K hAK m I (fun b : B => b.val)
    (fun b => (hB b.val b.property).1)
  · intro b
    rw [Polynomial.LeadingBaseChange.polynomial_leading_coefficient_map m _ hRA]
    apply IsLocalization.Away.isUnit_of_dvd s
    exact Finset.dvd_prod_of_mem (fun b : B => m.leadingCoeff b.val) (Finset.mem_univ b)
  · intro f hf hf0
    obtain ⟨b, hb, hbf⟩ := hcover f hf hf0
    exact ⟨⟨b, hb⟩, hbf⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericPolynomialQuotientFree.GradedHilbert
