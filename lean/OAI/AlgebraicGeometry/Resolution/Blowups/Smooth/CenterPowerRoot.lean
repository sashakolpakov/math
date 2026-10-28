import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatContainment
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DualCenterPowerRoot

/-! # Center Power Root -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPowerRoot.Construction

noncomputable section

/-! Exact power extraction along arbitrary smooth closed centers in characteristic zero. -/

universe u

variable (k : Type u) {R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing R] [Algebra k R] [Algebra.Smooth k R]

theorem smooth_center_ideal_power_root (I J : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (b e : ℕ) (he : 0 < e) (hJ : J ^ e ≤ I ^ (b * e)) : J ≤ I ^ b := by
  classical
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  apply Ideal.le_of_localization_maximal
  intro p hp
  let : p.IsMaximal := hp
  by_cases hIp : I ≤ p
  · obtain ⟨S, hSk, hSs, f, hf, q, hq, ι, hι, hdec, v, D, hD, hI⟩ :=
      CenterPointedFrame.Construction.smooth_center_pointed_frame (k := k) I ⟨p, inferInstance⟩ hIp
    let : Algebra ℚ S := ((algebraMap k S).comp (algebraMap ℚ k)).toAlgebra
    have hpow : (J.map f.toRingHom) ^ e ≤ (Ideal.span (Set.range v)) ^ (b * e) := by
      have h := Ideal.map_mono (f := f.toRingHom) hJ
      rwa [Ideal.map_pow, Ideal.map_pow, hI] at h
    have hlocal := DualCenterPowerRoot.Construction.smooth_dual_center_ideal_power_root k v D hD (J.map f.toRingHom) b e he hpow
    rw [← hI, ← Ideal.map_pow] at hlocal
    exact Pointed.FlatContainment.Construction.flat_map_ideal_containment_at_prime f.toRingHom
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1 J (I ^ b) p q.asIdeal
      (congrArg PrimeSpectrum.asIdeal hq) hlocal
  · rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime p) hIp,
      Ideal.top_pow]
    exact le_top

theorem smooth_center_weighted_iff (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (b : ℕ) (J : Fin b → Ideal R) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ I ^ b.factorial ↔ ∀ j, J j ≤ I ^ (b - j.val) := by
  constructor
  · intro h j
    have hj := (le_iSup (fun i => J i ^ WeightedCoefficientIdeal.Construction.coefficientWeight b i) j).trans h
    rw [← WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control b j] at hj
    exact smooth_center_ideal_power_root k I (J j) (b - j.val)
      (WeightedCoefficientIdeal.Construction.coefficientWeight b j) (WeightedCoefficientIdeal.Construction.coefficientWeight_pos b j) hj
  · exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow I b J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPowerRoot.Construction
