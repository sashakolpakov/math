import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceChart

/-! # Persistent Hypersurface -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PersistentHypersurface.Construction

noncomputable section

/-! Smooth derivative equations with persistence in the differential ideals of blowup transforms. -/

open _root_.MvPolynomial

variable {R : Type*} [CommRing R]

theorem iteratedRingDerivation_mem_differentialIdeal
    (Ds : List (Derivation ℤ R R)) (J : Ideal R) {p : R} (hp : p ∈ J) :
    DifferentialBlowupTransform.Construction.iteratedRingDerivation Ds p ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J Ds.length := by
  induction Ds generalizing J p with
  | nil => exact hp
  | cons D Ds ih =>
    exact ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J) (DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal J D hp)

variable {σ : Type*}

/-- Partial derivatives considered as integer-linear ring derivations. -/
def polynomialPartialDerivationInt (i : σ) :
    Derivation ℤ (MvPolynomial σ R) (MvPolynomial σ R) :=
  (pderiv i).restrictScalars ℤ

theorem iteratedRingDerivation_map_partial (l : List σ) (p : MvPolynomial σ R) :
    DifferentialBlowupTransform.Construction.iteratedRingDerivation (l.map (polynomialPartialDerivationInt (R := R))) p =
      DifferentialOrder.Construction.iteratedPDeriv l p := by
  induction l generalizing p with
  | nil => rfl
  | cons i l ih =>
    exact ih (pderiv i p)

/-- The explicit partial derivatives used to choose the hypersurface
belong to the corresponding differential ideal. -/
theorem iteratedPDeriv_mem_differentialIdeal (l : List σ) (J : Ideal (MvPolynomial σ R))
    {p : MvPolynomial σ R} (hp : p ∈ J) :
    DifferentialOrder.Construction.iteratedPDeriv l p ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J l.length := by
  induction l generalizing J p with
  | nil => exact hp
  | cons i l ih =>
    exact ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J)
      (DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal J (polynomialPartialDerivationInt i) hp)

variable {K : Type*} [Field K] [CharZero K] [Finite σ]

/-- At a point of positive exact ideal order, an actual smooth hypersurface
chart has an equation in the differential ideal of control one. -/
theorem exists_smooth_differential_hypersurface
    (J : Ideal (MvPolynomial σ K)) (x : σ → K) (n : ℕ)
    (hJ : J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (n + 1))
    (hJ1 : ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (n + 2)) :
    ∃ (q : MvPolynomial σ K) (i : σ),
      q ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n ∧ eval x q = 0 ∧ eval x (pderiv i q) ≠ 0 ∧
      Algebra.Smooth K (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q i) ∧
      (∃ e : HypersurfaceChart.Construction.hypersurfaceDerivativeChart q i →+* K,
        ∀ r : MvPolynomial σ K,
          e (algebraMap (HypersurfaceChart.Construction.hypersurfaceRing q) (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q i)
            (Ideal.Quotient.mk (Ideal.span {q}) r)) = eval x r) := by
  obtain ⟨p, l, i, hl, hz, hi, hs, he, _⟩ := HypersurfaceChart.Construction.exists_smooth_derivative_hypersurface J x n hJ hJ1
  refine ⟨DifferentialOrder.Construction.iteratedPDeriv l p.val, i, ?_, hz, hi, hs, he⟩
  simpa only [hl] using iteratedPDeriv_mem_differentialIdeal l J p.property

/-- The smooth derivative equation can be chosen with the algebraic
persistence property on every permissible actual affine blowup chart.
The conclusion records persistence of the differential equation, not the
smoothness of its transform for arbitrary centers. -/
theorem exists_smooth_persistent_hypersurface
    (J : Ideal (MvPolynomial σ K)) (x : σ → K) (n : ℕ)
    (hJ : J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (n + 1))
    (hJ1 : ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (n + 2)) :
    ∃ (q : MvPolynomial σ K) (i : σ),
      q ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n ∧ eval x q = 0 ∧ eval x (pderiv i q) ≠ 0 ∧
      Algebra.Smooth K (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q i) ∧
      ∀ (I : Ideal (MvPolynomial σ K)), J ≤ I ^ (n + 1) →
        ∃ hqI : q ∈ I, ∀ a : I,
          ExceptionalIdeal.Construction.blowupChartRatio I a ⟨q, hqI⟩ ∈
            DifferentialIdealTransform.Construction.iteratedDifferentialIdeal (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n := by
  obtain ⟨q, i, hq, hz, hi, hs, _⟩ := exists_smooth_differential_hypersurface J x n hJ hJ1
  refine ⟨q, i, hq, hz, hi, hs, ?_⟩
  intro I hI
  have hqI : q ∈ I := by
    have h := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J 1 n
      (by simpa only [Nat.add_comm 1 n] using hI) hq
    simpa only [pow_one] using h
  refine ⟨hqI, ?_⟩
  intro a
  exact DifferentialIdealTransform.Construction.blowupChart_differential_hypersurface_persists I J a ⟨q, hqI⟩ n hI hq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PersistentHypersurface.Construction
