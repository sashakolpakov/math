import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PrimeOrderNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Closed Point Chart Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport.Construction

noncomputable section

section

/-! Intrinsic differential order at closed points of arbitrary smooth affine algebras. -/

variable (k : Type*) {R : Type*} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

/-- The relative differential criterion holds on the original smooth
affine algebra, without choosing a global polynomial coordinate system. -/
theorem smooth_closedPoint_order_iff_relative_differentialIdeal (J q : Ideal R)
    [q.IsMaximal] (b : ℕ) :
    J.map (algebraMap R (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1) ↔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b ≤ q := by
  constructor
  · intro h
    have hpow := (ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (b + 1)).mp h
    have h := (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J b).trans
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow q J 1 b (by simpa only [Nat.add_comm] using hpow))
    simpa only [pow_one] using h
  · intro h
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
    have hdiff : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map φ) b ≤ Q := by
      rw [← DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange]
      exact (Ideal.map_mono h).trans hQle
    have hlocal := (Blowups.Etale.RelativeOrder.Construction.etale_closedPoint_order_iff_relative_differentialIdeal (σ := Fin d)
      (K := k) (J.map φ) Q b).mpr hdiff
    exact (Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff φ hφ J q Q hQ (b + 1)).mp hlocal

/-- The intrinsic relative ideal is a unit precisely when the prescribed
higher-order locus is empty at all closed points of the original smooth algebra. -/
theorem smooth_relative_differential_bound_iff_closedPoint_bound (J : Ideal R) (b : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b = ⊤ ↔
      ∀ (q : Ideal R) [q.IsMaximal],
        ¬ J.map (algebraMap R (Localization.AtPrime q)) ≤
          IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1) := by
  constructor
  · intro h q _ hq
    have hle := (smooth_closedPoint_order_iff_relative_differentialIdeal k J q b).mp hq
    rw [h] at hle
    exact (inferInstance : q.IsMaximal).ne_top (top_le_iff.mp hle)
  · intro h
    by_contra hproper
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hproper
    let : q.IsMaximal := hq
    exact h q ((smooth_closedPoint_order_iff_relative_differentialIdeal k J q b).mpr hle)

end

/-! Actual pointed étale coordinate charts and exact closed-point order transport. -/

theorem etale_closedPoint_global_order_iff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (J q : Ideal R) (Q : Ideal S)
    [q.IsMaximal] [Q.IsMaximal] (hQ : q = Q.comap f) (b : ℕ) :
    J.map f ≤ Q ^ b ↔ J ≤ q ^ b := by
  simpa only [ClosedWeightedOrder.Construction.closedPoint_local_order_iff] using Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff f hf J q Q hQ b

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- A closed point has a principal étale coordinate neighborhood and an
actual closed point above it, with the original ground algebra retained. -/
theorem exists_smooth_closed_point_coordinate_chart (q : Ideal R) [q.IsMaximal] :
    ∃ s ∉ q, ∃ (d : ℕ) (_ : Algebra (MvPolynomial (Fin d) k) (Localization.Away s)),
      IsScalarTower k (MvPolynomial (Fin d) k) (Localization.Away s) ∧
      Algebra.Etale (MvPolynomial (Fin d) k) (Localization.Away s) ∧
      ∃ Q : Ideal (Localization.Away s), Q.IsMaximal ∧ q = Q.comap (algebraMap R (Localization.Away s)) := by
  obtain ⟨s, hs, d, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q)
  let A := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) A := a
  let : IsScalarTower k (MvPolynomial (Fin d) k) A := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin d) k) A := he
  have hproper : q.map (algebraMap R A) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers s) A q).mpr
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs)
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (q.map (algebraMap R A)) hproper
  let : Q.IsMaximal := hQ
  have hp : (Q.comap (algebraMap R A)).IsPrime := inferInstance
  exact ⟨s, hs, d, a, ht, inferInstance, Q, hQ,
    (inferInstance : q.IsMaximal).eq_of_le hp.ne_top (Ideal.le_comap_of_map_le hle)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport.Construction
