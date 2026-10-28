import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy
import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Cone Chart Mem -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartMem.Constructions.ConeChartNormalization

noncomputable section

/-! # RiemannProjectivity: normalized coordinate ratios define the map from the chart algebra -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {ι : Type*} [Fintype ι]

def ratio (S : Set (ι → ℂ)) (i : ι) (j : {j : ι // j ≠ i}) : ConeChartBy.Constructions.ConeChartRestriction.patchRing S i :=
  algebraMap (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) (ConeChartBy.Constructions.ConeChartRestriction.variableClass S j.val) *
    IsLocalization.Away.invSelf (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)

omit [Fintype ι] in
theorem normalized_coordinates_mem (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (hcone : ∀ (c : ℂ) ⦃w⦄, w ∈ S → c • w ∈ S)
    (i : ι) (q : ConeChartBy.Constructions.ConeChartRestriction.patchRing S i →ₐ[ℂ] ℂ) :
    (fun j => q (ratio S i j)) ∈ ConeChartBy.Constructions.ConeChartRestriction.chart S i := by
  let qA := q.comp (Algebra.algHom ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i))
  let w := AffineVanishing.Constructions.AffineVanishingPoints.coordinates S qA
  have hw : w ∈ S := AffineVanishing.Constructions.AffineVanishingPoints.coordinates_mem S hS qA
  have hi : w i ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)).map q).ne_zero
  have hinv : q (IsLocalization.Away.invSelf (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)) = (w i)⁻¹ := by
    apply mul_left_cancel₀ hi
    rw [mul_inv_cancel₀ hi]
    change q (algebraMap (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)) *
      q (IsLocalization.Away.invSelf (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)) = 1
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have heq : AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (fun j => q (ratio S i j)) = (w i)⁻¹ • w := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [Pi.smul_apply, smul_eq_mul, hi]
    · rw [AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_of_ne i j _ hj]
      change q (algebraMap (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) (ConeChartBy.Constructions.ConeChartRestriction.variableClass S j) *
        IsLocalization.Away.invSelf (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)) = (w i)⁻¹ * w j
      rw [map_mul, hinv]
      exact mul_comm (w j) (w i)⁻¹
  change AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i (fun j => q (ratio S i j)) ∈ S
  rw [heq]
  exact hcone (w i)⁻¹ hw

theorem relation_zero (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (hcone : ∀ (c : ℂ) ⦃w⦄, w ∈ S → c • w ∈ S)
    (i : ι) (p : MvPolynomial {j : ι // j ≠ i} ℂ)
    (hp : p ∈ MvPolynomial.vanishingIdeal ℂ (ConeChartBy.Constructions.ConeChartRestriction.chart S i)) :
    MvPolynomial.aeval (ratio S i) p = 0 := by
  let : Algebra.FinitePresentation (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) :=
    IsLocalization.Away.finitePresentation (ConeChartBy.Constructions.ConeChartRestriction.variableClass S i)
  let : Algebra.FiniteType ℂ (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S))
      (inferInstance : Algebra.FiniteType (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) (ConeChartBy.Constructions.ConeChartRestriction.patchRing S i))
  apply CharacterSeparationEq.Constructions.CharacterSeparation.eq_zero_of_all_points_zero
  intro q
  have h := hp (fun j => q (ratio S i j)) (normalized_coordinates_mem S hS hcone i q)
  exact (MvPolynomial.comp_aeval_apply (ratio S i) q p).trans h

def normalization (S : Set (ι → ℂ))
    (hS : ∀ x, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ S, MvPolynomial.eval x p = 0) → x ∈ S)
    (hcone : ∀ (c : ℂ) ⦃w⦄, w ∈ S → c • w ∈ S) (i : ι) :
    AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart S i) →ₐ[ℂ] ConeChartBy.Constructions.ConeChartRestriction.patchRing S i :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (ratio S i)) (fun p hp => relation_zero S hS hcone i p hp)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartMem.Constructions.ConeChartNormalization
