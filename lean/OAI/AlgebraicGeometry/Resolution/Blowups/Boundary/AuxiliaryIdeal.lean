import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinatePower
import OAI.AlgebraicGeometry.Resolution.Blowups.CompanionCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Auxiliary Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryIdeal.Construction

noncomputable section

/-! An auxiliary marked ideal forcing centers into a chosen boundary intersection. -/

section

variable {R : Type*} [CommRing R]

/-- At control `m`, adjoin the `m`th power of the selected boundary-intersection ideal. -/
def boundaryAuxiliaryIdeal (J L : Ideal R) (m : ℕ) : Ideal R := J ⊔ L ^ m

/-- The auxiliary ideal's controlled transform preserves its marked-intersection form. -/
theorem blowup_boundaryAuxiliary_controlledTransform (I J L : Ideal R) (a : I) (m : ℕ)
    (hJ : J ≤ I ^ m) (hL : L ≤ I) :
    ControlledTransform.Construction.blowupControlledTransform I (boundaryAuxiliaryIdeal J L m) m a =
      boundaryAuxiliaryIdeal (ControlledTransform.Construction.blowupControlledTransform I J m a)
        (ControlledTransform.Construction.blowupControlledTransform I L 1 a) m := by
  simpa only [boundaryAuxiliaryIdeal, MarkedIdealIntersection.Construction.markedIdealIntersection, pow_one, Nat.mul_one] using
    MarkedIdealIntersection.Construction.blowup_markedIdealIntersection_controlledTransform I J L a m 1 hJ
      (by simpa only [pow_one] using hL)

/-- If the center parameter's control power is present, the corresponding
actual chart has unit controlled transform. -/
theorem blowupControlledTransform_eq_top_of_parameter_power (I J : Ideal R) (a : I) (m : ℕ)
    (ha : a.val ^ m ∈ J) : ControlledTransform.Construction.blowupControlledTransform I J m a = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  apply Ideal.mem_colon_span_singleton.mpr
  change 1 * Blowup.Charts.Construction.blowupChartConstants I a a.val ^ m ∈ J.map (Blowup.Charts.Construction.blowupChartConstants I a)
  rw [one_mul (Blowup.Charts.Construction.blowupChartConstants I a a.val ^ m), ← map_pow (Blowup.Charts.Construction.blowupChartConstants I a) a.val m]
  exact Ideal.mem_map_of_mem _ ha

end

universe u

variable {σ K S : Type u} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

omit [DecidableEq σ] [Algebra.Etale (MvPolynomial σ K) S] in
/-- Every chart whose denominator is one of the selected old boundary
coordinates clears the auxiliary ideal completely. -/
theorem etale_boundary_auxiliary_denominator_chart_unit
    (C B : Finset σ) (i : C) (hiB : i.val ∈ B) (J : Ideal S) (m : ℕ) :
    ControlledTransform.Construction.blowupControlledTransform (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
      (boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) m) m
      (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) = ⊤ := by
  apply blowupControlledTransform_eq_top_of_parameter_power
  apply Submodule.mem_sup_right
  exact Ideal.pow_mem_pow (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement (K := K) (S := S) B ⟨i.val, hiB⟩).property m

variable [CharZero K]

/-- A selected old boundary coordinate is a logarithmic maximal-contact
equation for the auxiliary ideal, relative to any retained boundary family
excluding that coordinate. Both the unit bound and persistence membership
come from its explicit included power. -/
theorem etale_boundary_auxiliary_logarithmic_equation
    (B L : Finset σ) (h : σ) (hhB : h ∈ B) (hhL : h ∉ L) (J : Ideal S) (m : ℕ) :
    let w := fun j : L => algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)
    let H := boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)
    LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w H (m + 1) = ⊤ ∧
      algebraMap (MvPolynomial σ K) S (MvPolynomial.X h) ∈ LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w H m := by
  let : Algebra ℚ S := ((algebraMap (MvPolynomial σ K) S).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  let w := fun j : L => algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)
  let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
  let H := boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)
  let D : LogarithmicDerivation.Construction.logarithmicDerivations w := ⟨Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) h, by
    intro j
    have hhj : h ≠ j.val := fun he => hhL (he.symm ▸ j.property)
    change Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) h
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)) ∈ Ideal.span {w j}
    rw [Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X, ite_eq_right hhj]
    exact Ideal.zero_mem _⟩
  have hDz : D.val z = 1 := by
    change Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) h
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)) = 1
    rw [Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X, ite_eq_left rfl]
  have hzm : z ^ (m + 1) ∈ H := Submodule.mem_sup_right
    (Ideal.pow_mem_pow (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement (K := K) (S := S) B ⟨h, hhB⟩).property (m + 1))
  exact ⟨LogarithmicCoordinatePower.Construction.logarithmic_bound_of_coordinate_power w D z hDz H (m + 1) hzm,
    LogarithmicCoordinatePower.Construction.coordinate_mem_logarithmic_of_power w D z hDz H m hzm⟩

variable [IsAlgClosed K] [Finite σ]

/-- Permissibility of the auxiliary ideal is exactly permissibility of
the original ideal together with containment of the center in the selected
boundary intersection. -/
theorem etale_boundary_auxiliary_center_iff (C : Finset σ) (J L : Ideal S) (m : ℕ) (hm : 0 < m) :
    let I := Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C
    boundaryAuxiliaryIdeal J L m ≤ I ^ m ↔ J ≤ I ^ m ∧ L ≤ I := by
  simpa only [boundaryAuxiliaryIdeal, MarkedIdealIntersection.Construction.markedIdealIntersection, pow_one, Nat.mul_one] using
    CompanionCenter.Construction.etale_coordinate_center_markedIntersection_iff C J L m 1 hm Nat.zero_lt_one

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryIdeal.Construction
