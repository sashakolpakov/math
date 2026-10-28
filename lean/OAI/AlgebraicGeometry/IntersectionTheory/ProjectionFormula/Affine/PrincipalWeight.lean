import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedTorEuler

/-! # Principal Weight -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeight

noncomputable section

/-! The principal quotient's generic-length weight is the genuine
geometric divisor order on the original affine reduced support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

variable (R : Type) [CommRing R] [IsNoetherianRing R] (v : PrimeSpectrum R) (r : R)

def weight (w : PrimeSpectrum R) : ℚ :=
  if h : v.asIdeal ≤ w.asIdeal then
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportStalk.support R v)).ord
      (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportStalk.support R v)).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage (SupportStalk.support R v) w (SupportStalk.mem R v w h)))
        (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportStalk.support R v)).functionField
          (Local.Principal.supportStalkMap (Spec (.of R)) (SupportStalk.support R v) w (SupportStalk.mem R v w h)
            (StructureSheaf.toStalk R w r))) (CycleClass.Thom.IntersectionGeometry.supportPreimage (SupportStalk.support R v) w (SupportStalk.mem R v w h)) : ℚ)
  else 0

theorem eq_length (hr : r ∉ v.asIdeal)
    (w : PrimeSpectrum R) (hw : w ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal))) :
    weight R v r w =
      ((FiltrationBaseLength.length R (Localization.AtPrime w.asIdeal)
        (.of R (QuotSMulTop r (R ⧸ v.asIdeal)))).toNat : ℚ) := by
  have hvw := (PrincipalCodimension.mem_support v w r hw).1
  rw [weight, dite_eq_left hvw]
  exact_mod_cast PrincipalBaseChange.SupportOrder.order R v w hvw r hr

theorem eq_length_all (hr : r ∉ v.asIdeal) (w : PrimeSpectrum R) :
    weight R v r w =
      ((FiltrationBaseLength.length R (Localization.AtPrime w.asIdeal)
        (.of R (QuotSMulTop r (R ⧸ v.asIdeal)))).toNat : ℚ) := by
  by_cases hvw : v.asIdeal ≤ w.asIdeal
  · rw [weight, dite_eq_left hvw]
    exact_mod_cast PrincipalBaseChange.SupportOrder.order R v w hvw r hr
  · have hw : w ∉ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal)) :=
      fun h => hvw (PrincipalCodimension.mem_support v w r h).1
    rw [weight, dite_eq_right hvw, LocalizedTorEuler.length_zero R _ w hw]
    rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeight
