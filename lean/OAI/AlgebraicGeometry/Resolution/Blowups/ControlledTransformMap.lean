import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Controlled Transform Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap.Construction

noncomputable section

/-! Functoriality of controlled ideals under coefficient extension on actual charts. -/

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- For a divisible ideal, its principal ideal quotient commutes with
extension whenever the image of the divisor is regular. -/
theorem map_colon_principal_of_divisible (J : Ideal R) (c : R) (φ : R →+* S)
    (hJ : J ≤ Ideal.span {c}) (hc : IsRegular (φ c)) :
    (J.colon (Ideal.span {c})).map φ = (J.map φ).colon (Ideal.span {φ c}) := by
  have hfactor := congrArg (Ideal.map φ) (ControlledTransform.Construction.principal_mul_colon_of_le J c hJ)
  rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hfactor
  rw [← hfactor, ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ hc]

/-- The total ideal commutes with the explicit coefficient-extension chart map. -/
theorem blowupChartMap_totalIdeal (I J : Ideal R) (a : I) (φ : R →+* S) :
    (J.map (Blowup.Charts.Construction.blowupChartConstants I a)).map (ChartLift.Construction.blowupChartMap I φ a) =
      (J.map φ).map
        (Blowup.Charts.Construction.blowupChartConstants (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro r
  exact ChartLift.Construction.blowupChartMap_constants I φ a r

/-- Controlled transforms of admissible ideals commute with coefficient
extension on corresponding actual Rees charts. -/
theorem blowupChartMap_controlledIdeal (I J : Ideal R) (a : I) (φ : R →+* S)
    (b : ℕ) (hJ : J ≤ I ^ b) :
    (ControlledTransform.Construction.blowupControlledTransform I J b a).map (ChartLift.Construction.blowupChartMap I φ a) =
      ControlledTransform.Construction.blowupControlledTransform (I.map φ) (J.map φ) b
        ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  have hreg : IsRegular (ChartLift.Construction.blowupChartMap I φ a (c ^ b)) := by
    rw [map_pow (ChartLift.Construction.blowupChartMap I φ a), ChartLift.Construction.blowupChartMap_constants]
    exact IsRegular.pow
      (a := Blowup.Charts.Construction.blowupChartConstants (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ (φ a.val)) b
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular (I.map φ)
        ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩)
  have hdiv := ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I J b a hJ
  have h := map_colon_principal_of_divisible (J.map (Blowup.Charts.Construction.blowupChartConstants I a)) (c ^ b)
    (ChartLift.Construction.blowupChartMap I φ a) hdiv hreg
  rw [blowupChartMap_totalIdeal, map_pow (ChartLift.Construction.blowupChartMap I φ a), ChartLift.Construction.blowupChartMap_constants] at h
  exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap.Construction
