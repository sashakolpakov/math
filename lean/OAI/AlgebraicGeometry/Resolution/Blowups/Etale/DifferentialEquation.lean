import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.TangentCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder

/-! # Differential Equation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DifferentialEquation.Construction

noncomputable section

/-! Differential equations with nonvanishing coordinate derivative on arbitrary étale affine ideals. -/

variable {R : Type*} [CommRing R]

theorem first_iteratedDifferentialIdeal (J : Ideal R) (n : ℕ) :
    DifferentialIdealTransform.Construction.firstDifferentialIdeal (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n) = DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J (n + 1) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih => exact ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J)

variable {σ K S : Type*} [Field K] [CommRing S]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

variable [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]

/-- Coordinate partial derivations of the étale ring relative to the coefficient field. -/
def etaleRelativePartial (i : σ) : Derivation K S S :=
  Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (MvPolynomial.pderiv i)

theorem etaleRelativePartial_algebraMap (i : σ) (p : MvPolynomial σ K) :
    etaleRelativePartial (K := K) (S := S) i (algebraMap (MvPolynomial σ K) S p) =
      algebraMap (MvPolynomial σ K) S (MvPolynomial.pderiv i p) :=
  Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (MvPolynomial.pderiv i) p

theorem etaleRelativePartial_restrictScalars (i : σ) :
    (etaleRelativePartial (K := K) (S := S) i).restrictScalars ℤ =
      LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) i := by
  refine Blowups.Etale.Derivation.Construction.etaleDerivation_ext (k := ℤ) (R := MvPolynomial σ K) (S := S) _ _ ?_
  intro p
  rw [Derivation.restrictScalars_apply, etaleRelativePartial_algebraMap]
  exact (Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (S := S) (PersistentHypersurface.Construction.polynomialPartialDerivationInt i) p).symm

variable [CharZero K] [Fintype σ] [DecidableEq σ]

/-- At a point of exact positive order, an arbitrary ideal on an étale
coordinate neighborhood has a differential equation with nonzero relative differential. -/
theorem exists_etale_differential_equation (J : Ideal S) (x : σ → K)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ)
    (hJ : J.map (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1))
    (hJ1 : ¬ J.map (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 2)) :
    ∃ (z : S) (i : σ), z ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n ∧ z ∈ q ∧
      etaleRelativePartial (K := K) i z ∉ q := by
  let H := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n
  have hH : H ≤ q := (LocalOrder.Construction.etale_local_order_iff_differentialIdeal J x q n).mp hJ
  have hfirst : ¬ DifferentialIdealTransform.Construction.firstDifferentialIdeal H ≤ q := by
    rw [first_iteratedDifferentialIdeal]
    exact fun h => hJ1 ((LocalOrder.Construction.etale_local_order_iff_differentialIdeal J x q (n + 1)).mpr h)
  have hH2 : ¬ H.map (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ 2 := by
    exact fun h => hfirst ((LocalOrder.Construction.etale_local_order_iff_differentialIdeal H x q 1).mp h)
  rw [Ideal.map_le_iff_le_comap] at hH2
  obtain ⟨z, hz, hz2⟩ := SetLike.not_le_iff_exists.mp hH2
  obtain ⟨i, hi⟩ := Coordinate.TangentCriterion.Construction.etale_exists_coordinate_derivative_not_mem x q z (hH hz) hz2
  refine ⟨z, i, hz, hH hz, ?_⟩
  have he := Derivation.congr_fun (etaleRelativePartial_restrictScalars (S := S) (K := K) i) z
  exact he ▸ hi

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DifferentialEquation.Construction
