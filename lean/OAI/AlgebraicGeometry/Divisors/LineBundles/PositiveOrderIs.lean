import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.LocalValuation
import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationOf

/-! # Positive Order Is -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveOrderIs.BundleCycles.PositiveOrder

noncomputable section

/-! Positive order in a DVR means that the rational function is an
actual element of the maximal ideal. This is the local input for covering
all zeros by the normalized zero-parameter model. -/

open _root_.AlgebraicGeometry

theorem stalk_isDVR {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  let : Ring.DimensionLEOne R := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let : IsDedekindDomain R :=
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }
  have hn : ¬ IsField R := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    change ringKrullDim (X.presheaf.stalk x) = 0 at hzero
    rw [ringKrullDim_stalk_eq_coheight, hx] at hzero
    exact (by decide : (1 : WithBot ℕ∞) ≠ 0) hzero
  have ht : IsDiscreteValuationRing R ↔ IsDedekindDomain R :=
    (IsDiscreteValuationRing.TFAE R hn).out 1 3
  exact ht.mpr inferInstance

theorem exists_maximalIdeal_element (R L : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field L] [Algebra R L] [IsFractionRing R L]
    (g : L) (hg : g ≠ 0) (hpos : 0 < WithZero.log (Ring.ordFrac R g)) :
    ∃ a : R, a ∈ IsLocalRing.maximalIdeal R ∧ algebraMap R L a = g := by
  have ho0 : Ring.ordFrac R g ≠ 0 := (map_ne_zero (Ring.ordFrac R (K := L))).mpr hg
  have ho : (1 : WithZero (Multiplicative ℤ)) < Ring.ordFrac R g := by
    simpa only [WithZero.exp_zero] using
      (WithZero.lt_log_iff_exp_lt ho0).mp hpos
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation L g ≤ 1 := by
    rw [Ring.ordFrac_eq_valuation_inv] at ho
    exact ((one_lt_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hg))).mp ho).le
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hv
  refine ⟨a, ?_, ha⟩
  change ¬ IsUnit a
  intro hu
  have he := Ring.ordFrac_of_isUnit (K := L) hu
  rw [ha] at he
  exact (ne_of_gt ho) he

theorem exists_stalk_element {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (g : X.functionField) (hg : g ≠ 0) (hpos : 0 < X.ord g x) :
    ∃ a : X.presheaf.stalk x, a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      algebraMap (X.presheaf.stalk x) X.functionField a = g := by
  have hx : Order.coheight x = 1 := by
    by_contra h
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hpos
    exact (lt_irrefl 0) hpos
  let := stalk_isDVR x hx
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx] at hpos
  exact exists_maximalIdeal_element (X.presheaf.stalk x) X.functionField g hg hpos

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveOrderIs.BundleCycles.PositiveOrder
