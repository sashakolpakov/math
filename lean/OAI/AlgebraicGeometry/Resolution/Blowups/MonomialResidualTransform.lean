import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Monomial
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Monomial Residual Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MonomialResidualTransform.Construction

noncomputable section

/-! Explicit exponent bookkeeping for an exceptional monomial times a residual ideal. -/

open _root_.MvPolynomial Finset

universe u

variable {σ R : Type u} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- Replacing one exponent isolates precisely the corresponding coordinate power. -/
theorem coordinateMonomial_update_factor (a : σ → ℕ) (i : σ) (k : ℕ) :
    MonomialBlowupChart.Construction.coordinateMonomial (R := R) (Function.update a i k) =
      X i ^ k * MonomialBlowupChart.Construction.coordinateMonomial (Function.update a i 0) := by
  have hform (n : ℕ) : MonomialBlowupChart.Construction.coordinateMonomial (R := R) (Function.update a i n) =
      X i ^ n * ∏ j ∈ univ.erase i, X j ^ a j := by
    rw [MonomialBlowupChart.Construction.coordinateMonomial, ← mul_prod_erase univ
      (fun j => (X j : MvPolynomial σ R) ^ Function.update a i n j) (mem_univ i), Function.update_self]
    congr 1
    apply prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (mem_erase.mp hj).1]
  rw [hform k, hform 0, pow_zero, one_mul]

/-- The residual control adds its excess to the new exceptional exponent. -/
def residualMonomialChartExponents (a : σ → ℕ) (m b : ℕ) (C : Finset σ) (i : σ) : σ → ℕ :=
  Function.update a i ((∑ j ∈ C, a j) + m - b)

variable {S : Type u} [CommRing S] [Algebra (MvPolynomial σ R) S]

omit [Fintype σ] in
/-- The new denominator coordinate is the actual exceptional parameter. -/
theorem etaleSubsetCoordinateMap_self (C : Finset σ) (i : C) :
    Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := R) (S := S) C i (X i.val) =
      Blowup.Charts.Construction.blowupChartConstants ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))
        ⟨algebraMap (MvPolynomial σ R) S (X i.val),
          Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩
        (algebraMap (MvPolynomial σ R) S (X i.val)) := by
  rw [Etale.MonomialStep.Construction.etaleSubsetCoordinateMap, RingHom.comp_apply, SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup_self,
    ChartLift.Construction.blowupChartMap_constants]

/-- The actual controlled transform of a monomial times a residual ideal
remains a monomial times the residual controlled transform. The new exponent
is the center's monomial order plus the residual control minus total control. -/
theorem etale_monomial_residual_controlledTransform
    (a : σ → ℕ) (J : Ideal S) (C : Finset σ) (i : C) (m b : ℕ)
    (hb : b ≤ (∑ j ∈ C, a j) + m)
    (hJ : J ≤ ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)) ^ m) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)
    let e : I := ⟨algebraMap (MvPolynomial σ R) S (X i.val),
      Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩
    let M := (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := R) a}).map (algebraMap (MvPolynomial σ R) S)
    ControlledTransform.Construction.blowupControlledTransform I (M * J) b e =
      Ideal.span {Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := R) (S := S) C i
        (MonomialBlowupChart.Construction.coordinateMonomial (residualMonomialChartExponents a m b C i.val))} *
        ControlledTransform.Construction.blowupControlledTransform I J m e := by
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)
  let e : I := ⟨algebraMap (MvPolynomial σ R) S (X i.val),
    Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩
  let M := (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := R) a}).map (algebraMap (MvPolynomial σ R) S)
  let w := ∑ j ∈ C, a j
  let φ := Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := R) (S := S) C i
  have hM : M ≤ I ^ w := by
    rw [← Ideal.map_pow]
    apply Ideal.map_mono
    exact (Ideal.span_singleton_le_iff_mem _).mpr (SubsetMonomialTransform.Construction.coordinateMonomial_mem_subset_center_power a C)
  have he := ResidualCoefficientTransform.Construction.blowup_product_controlledTransform I M J e w m b hb hM hJ
  have hm : ControlledTransform.Construction.blowupControlledTransform I M w e =
      Ideal.span {φ (MonomialBlowupChart.Construction.coordinateMonomial (R := R) (Function.update a i.val 0))} := by
    simpa only [MonomialTermination.Construction.monomialChartExponents, w, Nat.sub_self] using
      Etale.MonomialStep.Construction.etaleSubsetCoordinate_controlledIdeal (R := R) (S := S) a w C le_rfl i
  rw [hm, ← mul_assoc, Ideal.span_singleton_mul_span_singleton] at he
  have hf : (Blowup.Charts.Construction.blowupChartConstants I e e.val) ^ (w + m - b) *
      φ (MonomialBlowupChart.Construction.coordinateMonomial (R := R) (Function.update a i.val 0)) =
      φ (MonomialBlowupChart.Construction.coordinateMonomial (R := R) (residualMonomialChartExponents a m b C i.val)) := by
    change (Blowup.Charts.Construction.blowupChartConstants I e e.val) ^ (w + m - b) *
      φ (MonomialBlowupChart.Construction.coordinateMonomial (R := R) (Function.update a i.val 0)) =
      φ (MonomialBlowupChart.Construction.coordinateMonomial (R := R) (Function.update a i.val (w + m - b)))
    rw [coordinateMonomial_update_factor a i.val (w + m - b), map_mul,
      map_pow φ (X i.val) (w + m - b), etaleSubsetCoordinateMap_self]
  rw [hf] at he
  exact he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MonomialResidualTransform.Construction
