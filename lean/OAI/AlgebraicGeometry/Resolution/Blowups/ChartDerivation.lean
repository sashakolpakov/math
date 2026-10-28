import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrder
import Mathlib.Algebra.DualNumber

/-! # Chart Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ChartDerivation.Construction

noncomputable section

/-! Lifting exceptional multiples of derivations to actual blowup charts. -/

open TrivSqZeroExt

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A derivation gives an infinitesimal ring map, scaled by any target element. -/
def scaledDerivationDualMap (φ : R →+* S) (D : Derivation ℤ R R) (c : S) :
    R →+* DualNumber S where
  toFun r := ⟨φ r, c * φ (D r)⟩
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by
    apply TrivSqZeroExt.ext
    · exact map_add φ r s
    · change c * φ (D (r + s)) = c * φ (D r) + c * φ (D s)
      rw [map_add D, map_add φ, mul_add]
  map_mul' r s := by
    apply TrivSqZeroExt.ext
    · exact map_mul φ r s
    · change c * φ (D (r * s)) = φ r * (c * φ (D s)) + (c * φ (D r)) * φ s
      rw [D.leibniz]
      change c * φ (r * D s + s * D r) = _
      rw [map_add φ, map_mul φ, map_mul φ]
      ring

/-- A dual number whose first component is regular is itself regular. -/
theorem dualNumber_regular_of_fst (x : DualNumber S) (hx : IsRegular x.fst) : IsRegular x := by
  have hl : IsLeftRegular x := by
    intro y z h
    have hfst := congrArg TrivSqZeroExt.fst h
    simp only [fst_mul] at hfst
    have hyz : y.fst = z.fst := hx.left hfst
    apply TrivSqZeroExt.ext hyz
    apply hx.left
    have hsnd := congrArg TrivSqZeroExt.snd h
    simp only [DualNumber.snd_mul, hyz] at hsnd
    exact add_right_cancel hsnd
  exact ⟨hl, fun y z h => hl (by simpa only [mul_comm _ x] using h)⟩

def dualNumberFst : DualNumber S →+* S where
  toFun := TrivSqZeroExt.fst
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable (I : Ideal R) (a : I) (D : Derivation ℤ R R)

local instance : IsCentralScalar (Blowup.Charts.Construction.blowupChart I a) (Blowup.Charts.Construction.blowupChart I a) := by
  constructor
  intro x y
  change y * x = x * y
  exact mul_comm y x

local instance : CommRing (DualNumber (Blowup.Charts.Construction.blowupChart I a)) := TrivSqZeroExt.commRing

/-- The coefficient map with first-order term `a D`. -/
def blowupChartDualBase : R →+* DualNumber (Blowup.Charts.Construction.blowupChart I a) :=
  scaledDerivationDualMap (Blowup.Charts.Construction.blowupChartConstants I a) D (Blowup.Charts.Construction.blowupChartConstants I a a.val)

theorem blowupChartDualBase_center :
    I.map (blowupChartDualBase I a D) = Ideal.span {blowupChartDualBase I a D a.val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change blowupChartDualBase I a D r ∈ Ideal.span {blowupChartDualBase I a D a.val}
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨ExceptionalIdeal.Construction.blowupChartRatio I a ⟨r, hr⟩,
      Blowup.Charts.Construction.blowupChartConstants I a (D r) -
        Blowup.Charts.Construction.blowupChartConstants I a (D a.val) * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨r, hr⟩⟩, ?_⟩
    apply TrivSqZeroExt.ext
    · exact (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a ⟨r, hr⟩).symm
    · change Blowup.Charts.Construction.blowupChartConstants I a a.val * Blowup.Charts.Construction.blowupChartConstants I a (D r) =
        Blowup.Charts.Construction.blowupChartConstants I a a.val *
            (Blowup.Charts.Construction.blowupChartConstants I a (D r) -
              Blowup.Charts.Construction.blowupChartConstants I a (D a.val) * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨r, hr⟩) +
          (Blowup.Charts.Construction.blowupChartConstants I a a.val * Blowup.Charts.Construction.blowupChartConstants I a (D a.val)) *
            ExceptionalIdeal.Construction.blowupChartRatio I a ⟨r, hr⟩
      ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ a.property

theorem blowupChartDualBase_regular : IsRegular (blowupChartDualBase I a D a.val) :=
  dualNumber_regular_of_fst (blowupChartDualBase I a D a.val)
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)

/-- The affine-chart universal property lifts the infinitesimal coefficient map. -/
def blowupChartDualLift : Blowup.Charts.Construction.blowupChart I a →+* DualNumber (Blowup.Charts.Construction.blowupChart I a) :=
  @ChartLift.Construction.blowupChartLift R (DualNumber (Blowup.Charts.Construction.blowupChart I a)) _ _ I a (blowupChartDualBase I a D)
    (blowupChartDualBase_center I a D) (blowupChartDualBase_regular I a D)

theorem blowupChartDualLift_constants (r : R) :
    blowupChartDualLift I a D (Blowup.Charts.Construction.blowupChartConstants I a r) =
      blowupChartDualBase I a D r :=
  @ChartLift.Construction.blowupChartLift_constants R (DualNumber (Blowup.Charts.Construction.blowupChart I a)) _ _ I a (blowupChartDualBase I a D)
    (blowupChartDualBase_center I a D) (blowupChartDualBase_regular I a D) r

/-- The lifted infinitesimal map reduces to the identity modulo the square-zero direction. -/
theorem blowupChartDualLift_fst (x : Blowup.Charts.Construction.blowupChart I a) :
    (blowupChartDualLift I a D x).fst = x := by
  have he : (dualNumberFst (S := Blowup.Charts.Construction.blowupChart I a)).comp (blowupChartDualLift I a D) =
      RingHom.id _ := by
    apply ChartLift.Construction.blowupChart_hom_ext I a (Blowup.Charts.Construction.blowupChartConstants I a)
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
    · intro r
      change (blowupChartDualLift I a D (Blowup.Charts.Construction.blowupChartConstants I a r)).fst = _
      rw [blowupChartDualLift_constants]
      rfl
    · intro r
      rfl
  exact congrArg (fun f : Blowup.Charts.Construction.blowupChart I a →+* Blowup.Charts.Construction.blowupChart I a => f x) he

/-- The derivation `a D` on the coefficient ring extends to the actual chart. -/
def blowupChartDerivation : Derivation ℤ (Blowup.Charts.Construction.blowupChart I a) (Blowup.Charts.Construction.blowupChart I a) where
  toFun x := (blowupChartDualLift I a D x).snd
  map_add' x y := by rw [map_add, snd_add]
  map_smul' n x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    change (blowupChartDualLift I a D ((n : Blowup.Charts.Construction.blowupChart I a) * x)).snd =
      (n : Blowup.Charts.Construction.blowupChart I a) * (blowupChartDualLift I a D x).snd
    have hn : blowupChartDualLift I a D (n : Blowup.Charts.Construction.blowupChart I a) =
        (n : DualNumber (Blowup.Charts.Construction.blowupChart I a)) := map_intCast (blowupChartDualLift I a D) n
    rw [map_mul, hn]
    change (n : Blowup.Charts.Construction.blowupChart I a) * (blowupChartDualLift I a D x).snd +
      0 * (blowupChartDualLift I a D x).fst =
        (n : Blowup.Charts.Construction.blowupChart I a) * (blowupChartDualLift I a D x).snd
    ring
  map_one_eq_zero' := by
    change (blowupChartDualLift I a D 1).snd = 0
    rw [map_one, snd_one]
  leibniz' x y := by
    change (blowupChartDualLift I a D (x * y)).snd =
      x * (blowupChartDualLift I a D y).snd + y * (blowupChartDualLift I a D x).snd
    rw [map_mul]
    change (blowupChartDualLift I a D x).fst * (blowupChartDualLift I a D y).snd +
      (blowupChartDualLift I a D x).snd * (blowupChartDualLift I a D y).fst = _
    rw [blowupChartDualLift_fst, blowupChartDualLift_fst]
    rw [mul_comm (blowupChartDualLift I a D x).snd y]

theorem blowupChartDerivation_constants (r : R) :
    blowupChartDerivation I a D (Blowup.Charts.Construction.blowupChartConstants I a r) =
      Blowup.Charts.Construction.blowupChartConstants I a a.val * Blowup.Charts.Construction.blowupChartConstants I a (D r) := by
  change (blowupChartDualLift I a D (Blowup.Charts.Construction.blowupChartConstants I a r)).snd = _
  rw [blowupChartDualLift_constants]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ChartDerivation.Construction
