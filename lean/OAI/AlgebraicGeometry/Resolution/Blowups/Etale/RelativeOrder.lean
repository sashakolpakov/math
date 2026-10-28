import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EulerOrderCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations

/-! # Relative Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeOrder.Construction

noncomputable section

/-! Relative differential order on actual étale local rings and closed points. -/

variable {σ K S : Type*} [Field K] [CharZero K] [CommRing S] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]

/-- At an actual rational point, relative differential equations on
the original affine ring detect ideal order in its local ring. -/
theorem etale_local_order_iff_relative_differentialIdeal
    (J : Ideal S) (x : σ → K) (q : Ideal S) [q.IsPrime]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (b : ℕ) :
    J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1) ↔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K J b ≤ q := by
  let T := Localization.AtPrime q
  let : Algebra ℚ T := ((algebraMap (MvPolynomial σ K) T).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let z : σ → S := LocalOrder.Construction.etaleCenteredCoordinate x
  let D : σ → Derivation K S S := DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S)
  have hD : ∀ i j, D i (z j) = if i = j then 1 else 0 := by
    intro i j
    exact (Derivation.congr_fun (DifferentialEquation.Construction.etaleRelativePartial_restrictScalars (K := K) (S := S) i) (z j)).trans
      (LocalOrder.Construction.etalePolynomialCoordinateDerivation_centered x i j)
  have hM : Ideal.span (Set.range (fun i => algebraMap S T (z i))) = IsLocalRing.maximalIdeal T := by
    rw [LocalCoordinates.Construction.etale_local_maximalIdeal_eq_span_coordinates x q]
    apply congrArg (fun w : σ → T => Ideal.span (Set.range w))
    funext i
    exact (IsScalarTower.algebraMap_apply (MvPolynomial σ K) S T
      (MvPolynomial.X i - MvPolynomial.C (x i))).symm
  have h := Relative.EulerOrderCriterion.Construction.mapped_coordinate_order_iff_relative_differentialIdeal (B := T) z D hD J b
  rw [hM] at h
  have hq : (IsLocalRing.maximalIdeal T).comap (algebraMap S T) = q :=
    Localization.AtPrime.under_maximalIdeal (I := q)
  simpa only [Ideal.map_le_iff_le_comap, hq] using h

variable [IsAlgClosed K]

include σ in
/-- The relative differential criterion holds at every closed point. -/
theorem etale_closedPoint_order_iff_relative_differentialIdeal
    (J q : Ideal S) [q.IsMaximal] (b : ℕ) :
    J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1) ↔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K J b ≤ q := by
  obtain ⟨x, hx⟩ := ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  exact etale_local_order_iff_relative_differentialIdeal J x q b

include σ in
/-- The relative ideal carries exactly the same global order bound as
the previously verified ordinary differential ideal. -/
theorem etale_relative_differential_top_iff (J : Ideal S) (b : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K J b = ⊤ ↔ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b = ⊤ := by
  constructor
  · intro h
    apply top_unique
    rw [← h]
    exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary K J b
  · intro h
    by_contra hproper
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hproper
    let : q.IsMaximal := hq
    have hlocal := (etale_closedPoint_order_iff_relative_differentialIdeal (σ := σ) J q b).mpr hle
    have hord := (ClosedOrder.Construction.etale_closedPoint_order_iff_differentialIdeal (σ := σ) (K := K) J q b).mp hlocal
    rw [h] at hord
    exact hq.ne_top (top_le_iff.mp hord)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeOrder.Construction
