import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialStep
import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform

/-! # Coefficient Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep.Construction

noncomputable section

/-! Coefficient-transform reduction on all coordinate-compatible étale blowup charts. -/

universe u

variable {R : Type u} [CommRing R]

theorem blowupChartRatio_self (I : Ideal R) (a : I) : ExceptionalIdeal.Construction.blowupChartRatio I a a = 1 := by
  apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
  change Blowup.Charts.Construction.blowupChartConstants I a a.val * ExceptionalIdeal.Construction.blowupChartRatio I a a =
    Blowup.Charts.Construction.blowupChartConstants I a a.val * 1
  rw [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio, mul_one (Blowup.Charts.Construction.blowupChartConstants I a a.val)]

/-- The chart whose denominator is the persistent hypersurface equation
has empty transformed order locus at every proper ideal. -/
theorem persistent_hypersurface_denominator_chart_empty (I J : Ideal R) (z : I) (n : ℕ)
    (hJ : J ≤ I ^ (n + 1)) (hzJ : z.val ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I z)) (hM : M ≠ ⊤) :
    ¬ ControlledTransform.Construction.blowupControlledTransform I J (n + 1) z ≤ M ^ (n + 1) := by
  intro h
  have hz := DifferentialIdealTransform.Construction.blowupChart_differential_hypersurface_persists I J z z n hJ hzJ
  rw [blowupChartRatio_self] at hz
  have hpow := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow M (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) z) 1 n
    (by simpa only [Nat.add_comm 1 n] using h)
  rw [pow_one] at hpow
  exact hM (M.eq_top_of_isUnit_mem (hpow hz) isUnit_one)

variable {σ K S : Type u} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

theorem etalePolynomialCoordinateDerivation_X (i j : σ) :
    LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) i
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j)) = if i = j then 1 else 0 := by
  simpa only [LocalOrder.Construction.etaleCenteredCoordinate, MvPolynomial.C_0, sub_zero] using
    LocalOrder.Construction.etalePolynomialCoordinateDerivation_centered (S := S) (fun _ : σ => (0 : K)) i j

abbrev etaleCoordinateIdeal (C : Finset σ) : Ideal S :=
  (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)

abbrev etaleCoordinateElement (C : Finset σ) (i : C) : etaleCoordinateIdeal (K := K) (S := S) C :=
  ⟨algebraMap (MvPolynomial σ K) S (MvPolynomial.X i.val),
    Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := K) C i).property⟩

variable [CharZero K] [Fintype σ]

/-- On every other actual chart of a coordinate-compatible center, the
entire transformed order locus is exactly the controlled coefficient-order
locus on the persistent hypersurface. The denominator derivative vanishes
because its coordinate differs from the hypersurface coordinate. -/
theorem etale_coordinate_blowup_order_iff_coefficients
    (C : Finset σ) (i h : C) (hih : i.val ≠ h.val) (J : Ideal S) (n : ℕ)
    (hJ : J ≤ etaleCoordinateIdeal (K := K) (S := S) C ^ (n + 1))
    (hzJ : algebraMap (MvPolynomial σ K) S (MvPolynomial.X h.val) ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n)
    (M : Ideal (MonomialStep.Construction.etaleSubsetCoordinateChart (R := K) (S := S) C i)) :
    let I := etaleCoordinateIdeal (K := K) (S := S) C
    let a := etaleCoordinateElement (K := K) (S := S) C i
    let z := etaleCoordinateElement (K := K) (S := S) C h
    let D := LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) h.val
    ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a ≤ M ^ (n + 1) ↔
      ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M ∧ ∀ j < n + 1,
        ((DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z.val J j).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
          (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
            (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (n + 1 - j)}) ≤
          M.map (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})) ^ (n + 1 - j) := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  let : Algebra ℚ S := ((algebraMap (MvPolynomial σ K) S).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  apply NoetherianCoordinateTransform.Construction.noetherian_blowup_order_locus_iff_coefficient_transforms
  · simpa only [ite_eq_right (Ne.symm hih)] using
      etalePolynomialCoordinateDerivation_X (K := K) (S := S) h.val i.val
  · have hd := etalePolynomialCoordinateDerivation_X (K := K) (S := S) h.val h.val
    rw [ite_eq_left rfl] at hd
    exact hd
  · exact hJ
  · exact hzJ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep.Construction
