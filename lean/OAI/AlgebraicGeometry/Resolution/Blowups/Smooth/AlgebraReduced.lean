import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCenterReduced
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Algebra Reduced -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced.Construction

noncomputable section

/-! Reducedness of smooth algebras over an algebraically closed field from actual étale neighborhoods. -/

variable (k : Type*) {R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

include k in
/-- A smooth algebra over an algebraically closed field is reduced. The proof
uses actual principal étale neighborhoods and the checked local order theorem. -/
theorem smooth_algebra_isReduced : IsReduced R := by
  constructor
  intro x hx
  apply eq_zero_of_localization x
  intro q hq
  obtain ⟨s, hs, n, pAlg, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q)
  let : Algebra (MvPolynomial (Fin n) k) (Localization.Away s) := pAlg
  let : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away s) := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away s) := he
  let : IsReduced (Localization.Away s) := Etale.CoordinateCenterReduced.Construction.etale_polynomial_isReduced (σ := Fin n) (K := k)
  have hzero : algebraMap R (Localization.Away s) x = 0 :=
    (hx.map (algebraMap R (Localization.Away s))).eq_zero
  have hunit : IsUnit (algebraMap R (Localization.AtPrime q) s) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨s, hs⟩ : q.primeCompl)
  let g : Localization.Away s →+* Localization.AtPrime q :=
    IsLocalization.Away.lift (g := algebraMap R (Localization.AtPrime q)) s hunit
  have h := congrArg g hzero
  rw [IsLocalization.Away.lift_eq, map_zero] at h
  exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced.Construction
