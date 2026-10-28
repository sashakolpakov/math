import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PrimeOrderNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Closed Point Power Root -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointPowerRoot.Construction

noncomputable section

/-! Exact ideal power tests at closed points of arbitrary smooth affine algebras. -/

variable (k : Type*) {R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

include k in
/-- Smooth local rings have exact power scaling at every closed point,
without a fixed polynomial presentation of the original affine algebra. -/
theorem smooth_closedPoint_ideal_power_root (J q : Ideal R) [q.IsMaximal]
    (b e : ℕ) (he : 0 < e) (hJ : J ^ e ≤ q ^ (b * e)) : J ≤ q ^ b := by
  obtain ⟨s, hs, d, pAlg, ht, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q)
  let A := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) A := pAlg
  let : IsScalarTower k (MvPolynomial (Fin d) k) A := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin d) k) A := hEtale
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway s
  let φ := algebraMap R A
  have hφ : φ.Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hne : q.map φ ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers s) A q).mpr
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs)
  obtain ⟨Q, hQmax, hQle⟩ := Ideal.exists_le_maximal (q.map φ) hne
  let : Q.IsMaximal := hQmax
  have hQprime : (Q.comap φ).IsPrime := inferInstance
  have hQ : q = Q.comap φ := (inferInstance : q.IsMaximal).eq_of_le
    hQprime.ne_top (Ideal.le_comap_of_map_le hQle)
  obtain ⟨x, hx⟩ := Blowups.Etale.ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (σ := Fin d) (K := k) Q
  let : Q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  have hlocal := (ClosedWeightedOrder.Construction.closedPoint_local_order_iff (J ^ e) q (b * e)).mpr hJ
  have hmap := (Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff φ hφ (J ^ e) q Q hQ (b * e)).mpr hlocal
  rw [Ideal.map_pow, Ideal.map_pow] at hmap
  have hroot := (Blowups.Etale.PowerOrder.Construction.etale_local_ideal_pow_le_pow_iff x Q
    ((J.map φ).map (algebraMap A (Localization.AtPrime Q))) b e he).mp hmap
  exact (ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q b).mp
    ((Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff φ hφ J q Q hQ b).mp hroot)

include k in
/-- The weighted factorial control has exactly the original component
controls at every closed point of a smooth affine algebra. -/
theorem smooth_closedPoint_weighted_order_iff (q : Ideal R) [q.IsMaximal]
    (b : ℕ) (J : Fin b → Ideal R) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ q ^ b.factorial ↔ ∀ j, J j ≤ q ^ (b - j.val) := by
  constructor
  · intro h j
    have hj := (le_iSup (fun i => J i ^ WeightedCoefficientIdeal.Construction.coefficientWeight b i) j).trans h
    rw [← WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control b j] at hj
    exact smooth_closedPoint_ideal_power_root k (J j) q (b - j.val)
      (WeightedCoefficientIdeal.Construction.coefficientWeight b j) (WeightedCoefficientIdeal.Construction.coefficientWeight_pos b j) hj
  · exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow q b J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointPowerRoot.Construction
