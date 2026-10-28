import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTheta

/-! # Scalar Weights -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarWeights.CM

noncomputable section

/-! The source scalar determinant has its prescribed active exponent
and all compact-place sign exponents, in the original ordered places. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (places : GeometricSource.CM.Places E) (d : Gal(E/ℚ) → Bool) (r : Eˣ)
  (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)

include hr in
theorem conjugate_embedding (τ : Gal(E/ℚ)) :
    (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) (r : E) : E) : ℂ) = ((τ (r : E) : E) : ℂ)⁻¹ := by
  rw [(ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ).eq]
  change ((τ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E)) : E) : ℂ) = _
  rw [ScalarTheta.CM.conjugate_eq_inverse E r hr, map_inv₀, IntermediateField.coe_inv]

include hr in
theorem active_product : (∏ j : Fin 3, ScalarDeterminant.CM.weight E places d r (places.distinguished, j)) = (r : ℂ)⁻¹ := by
  have hn : (r : ℂ) ≠ 0 := (map_ne_zero E.val.toRingHom).mpr (Units.ne_zero r)
  have h0 : ScalarDeterminant.CM.weight E places d r (places.distinguished, 0) = (r : ℂ) := by
    simp [ScalarDeterminant.CM.weight, places.identity]
  have hj (j : Fin 3) (hj : j ≠ 0) : ScalarDeterminant.CM.weight E places d r (places.distinguished, j) =
      (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative places.distinguished) (r : E) : E) : ℂ) := by
    simp [ScalarDeterminant.CM.weight, hj]
  rw [Fin.prod_univ_three, h0, hj 1 (by decide), hj 2 (by decide),
    conjugate_embedding E r hr, places.identity, AlgEquiv.one_apply]
  field_simp

include hr in
theorem compact_product (i : Fin places.count) (hi : i ≠ places.distinguished) :
    (∏ j : Fin 3, ScalarDeterminant.CM.weight E places d r (i, j)) =
      ((places.representative i (r : E) : E) : ℂ) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d (places.representative i))) := by
  simp only [ScalarDeterminant.CM.weight, ite_eq_right hi]
  cases d (places.representative i)
  · change (∏ _j : Fin 3, ((places.representative i (r : E) : E) : ℂ)) =
      ((places.representative i (r : E) : E) : ℂ) ^ (3 : ℤ)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_ofNat]
  · change (∏ _j : Fin 3, (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i) (r : E) : E) : ℂ)) =
      ((places.representative i (r : E) : E) : ℂ) ^ (-3 : ℤ)
    rw [conjugate_embedding E r hr]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_neg, zpow_ofNat, inv_pow]

include hr in
theorem product :
    (∏ p, ScalarDeterminant.CM.weight E places d r p) = (r : ℂ)⁻¹ *
      ∏ i ∈ Finset.univ.erase places.distinguished,
        ((places.representative i (r : E) : E) : ℂ) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d (places.representative i))) := by
  rw [Fintype.prod_prod_type]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∏ j : Fin 3, ScalarDeterminant.CM.weight E places d r (i, j))
    (Finset.mem_univ places.distinguished), active_product E places d r hr]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact compact_product E places d r hr i (Finset.mem_erase.mp hi).1

variable {places d} {B : GeometricSource.CM.BallDatum E} (L : GeometricSource.CM.LinePeriod E B places d)

theorem halfDet_square (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks
        (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) ^ 2 =
      (r : ℂ)⁻¹ * ∏ i ∈ Finset.univ.erase places.distinguished,
        ((places.representative i (r : E) : E) : ℂ) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d (places.representative i))) :=
  (ScalarDeterminant.CM.halfDet_square E r L hr z hz).trans (product E places d r hr)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarWeights.CM
