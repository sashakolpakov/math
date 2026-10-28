import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Normal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.KrullDimension.Field

/-! # Generic Unit -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.GenericUnit

noncomputable section

/-! A rational function of order zero at a divisor is represented by an
actual unit of its generic ambient stalk. Smoothness supplies the DVR. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

theorem stalk_dvr (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport 1) :
    letI := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    IsDiscreteValuationRing (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
  let : IsIntegrallyClosed R := Smooth.Normal.stalk_integrallyClosed X.structureMap _
  have hx := CurveSupports.coheight_one X m A
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  let : Ring.DimensionLEOne R := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let : IsDedekindDomain R :=
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }
  have hdim : ringKrullDim R = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]
    rfl
  have hnf : ¬ IsField R := by
    intro h
    have he := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at he
    exact one_ne_zero he
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 3).mpr (inferInstance : IsDedekindDomain R)

theorem exists_unit_of_order_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0) :
    ∃ a : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val), IsUnit a ∧
      algebraMap (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) X.carrier.functionField a = f := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
  let : IsDiscreteValuationRing R := stalk_dvr X m A
  have hx := CurveSupports.coheight_one X m A
  have hfrac : Ring.ordFrac R f = 1 := by
    exact (Scheme.ord_eq_iff hx hf).mp hord
  have hmem : f ∈ MonoidHom.mker (Ring.ordFrac R) := hfrac
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
  exact hmem

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.GenericUnit
