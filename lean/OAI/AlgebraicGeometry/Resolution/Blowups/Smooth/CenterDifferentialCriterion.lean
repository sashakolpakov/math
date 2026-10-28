import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatContainment
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EulerOrderCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Center Differential Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterDifferentialCriterion.Construction

noncomputable section

/-! Intrinsic relative differential ideals detect exact powers of every smooth closed center. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [IsNoetherianRing R]

theorem smooth_center_order_iff_relative_differentialIdeal
    (I J : Ideal R) [Algebra.Smooth k (R ⧸ I)] (n : ℕ) :
    J ≤ I ^ (n + 1) ↔ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ I := by
  constructor
  · intro h
    apply (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J n).trans
    simpa only [pow_one] using DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J 1 n
      (by simpa only [Nat.add_comm 1 n] using h)
  · intro h
    apply Ideal.le_of_localization_maximal
    intro p hp
    let : p.IsMaximal := hp
    by_cases hIp : I ≤ p
    · obtain ⟨S, hSk, hSs, f, hf, q, hq, ι, hι, hdec, v, D, hD, hI⟩ :=
        CenterPointedFrame.Construction.smooth_center_pointed_frame (k := k) I ⟨p, inferInstance⟩ hIp
      let : Algebra ℚ S := (f.toRingHom.comp (algebraMap ℚ R)).toAlgebra
      have hd : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n ≤
          Ideal.span (Set.range v) := by
        rw [← DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J n, ← hI]
        exact Ideal.map_mono h
      have hc : J.map f.toRingHom ≤ Ideal.span (Set.range v) ^ (n + 1) := by
        have hself := (Relative.EulerOrderCriterion.Construction.mapped_coordinate_order_iff_relative_differentialIdeal
          (B := S) v D hD (J.map f.toRingHom) n)
        simp only [Algebra.algebraMap_self, Ideal.map_id, RingHom.id_apply] at hself
        exact hself.mpr hd
      rw [← hI, ← Ideal.map_pow] at hc
      exact Pointed.FlatContainment.Construction.flat_map_ideal_containment_at_prime f.toRingHom
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1 J (I ^ (n + 1)) p q.asIdeal
        (congrArg PrimeSpectrum.asIdeal hq) hc
    · rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime p) hIp,
        Ideal.top_pow]
      exact le_top

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterDifferentialCriterion.Construction
