import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform

/-! # Subcenter Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterMap.Construction

noncomputable section

/-! Maps of actual blowup charts when the target center also includes a normal coordinate. -/

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hIJ : I.map φ ≤ J) (a : I)

def subcenterDenominator : J := ⟨φ a.val, hIJ (Ideal.mem_map_of_mem φ a.property)⟩

/-- On the corresponding ambient chart the smaller center is also generated
by the exceptional parameter, since its chosen denominator lies in that center. -/
theorem subcenter_chart_ideal_principal :
    I.map ((Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a)).comp φ) =
      Ideal.span {Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a) (φ a.val)} := by
  rw [← Ideal.map_map]
  apply le_antisymm
  · have h : I.map φ ≤ J ^ 1 := by simpa only [pow_one] using hIJ
    calc
      (I.map φ).map (Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a)) ≤
          Ideal.span {(Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a) (φ a.val)) ^ 1} :=
        ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower J (I.map φ) 1
          (subcenterDenominator I J φ hIJ a) h
      _ = _ := congrArg
        (fun c : Charts.Construction.blowupChart J (subcenterDenominator I J φ hIJ a) => Ideal.span {c})
        (pow_one (Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a) (φ a.val)))
  · apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem φ a.property)

/-- The smaller center's blowup chart maps into the ambient blowup chart. -/
def blowupSubcenterMap : Charts.Construction.blowupChart I a →+* Charts.Construction.blowupChart J (subcenterDenominator I J φ hIJ a) :=
  ChartLift.Construction.blowupChartLift I a ((Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a)).comp φ)
    (subcenter_chart_ideal_principal I J φ hIJ a)
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular J (subcenterDenominator I J φ hIJ a))

theorem blowupSubcenterMap_constants (r : R) :
    blowupSubcenterMap I J φ hIJ a (Charts.Construction.blowupChartConstants I a r) =
      Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a) (φ r) :=
  ChartLift.Construction.blowupChartLift_constants _ _ _ _ _ r

/-- The smaller exceptional parameter maps to the actual ambient exceptional parameter. -/
theorem blowupSubcenterMap_exceptional :
    blowupSubcenterMap I J φ hIJ a (Charts.Construction.blowupChartConstants I a a.val) =
      Charts.Construction.blowupChartConstants J (subcenterDenominator I J φ hIJ a)
        (subcenterDenominator I J φ hIJ a).val :=
  blowupSubcenterMap_constants I J φ hIJ a a.val

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterMap.Construction
