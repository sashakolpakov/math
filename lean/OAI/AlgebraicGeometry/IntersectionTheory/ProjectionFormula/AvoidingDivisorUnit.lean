import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoheightOneCodimension

/-! # Avoiding Divisor Unit -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AvoidingDivisorUnit

noncomputable section

/-! If all divisor orders through a support vanish, the rational function
is an actual unit at its generic stalk. Normality detects this from the
height-one localizations, in every ambient dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_unit_at (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (x : X.carrier) (f : X.carrier.functionField) (hf : f ≠ 0)
    (ho : ∀ p : Spec (X.carrier.presheaf.stalk x), p.asIdeal.height = 1 →
      X.carrier.ord f (X.carrier.fromSpecStalk x p) = 0) :
    ∃ a : X.carrier.presheaf.stalk x, IsUnit a ∧
      algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField a = f := by
  let R := X.carrier.presheaf.stalk x
  let K := X.carrier.functionField
  let : IsIntegrallyClosed R := Smooth.Normal.stalk_integrallyClosed X.structureMap x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R f
  have hb₀ : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha₀ : a ≠ 0 := by
    intro ha
    apply hf
    rw [← hab, ha, map_zero, zero_div]
  have hfa : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha₀
  have hfb : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb₀
  have hass : Associated b a := by
    apply NormalDivisibility.associated_of_orders R b a hb₀ ha₀
    intro p hprime hp
    let S := Localization.AtPrime p
    let : IsDiscreteValuationRing S := NormalDivisibility.localization_dvr R p hp
    have hi : Function.Injective (algebraMap R S) :=
      IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
    have hna := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hi).mpr ha₀))
    have hnb := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hi).mpr hb₀))
    have hz := ho ⟨p, hprime⟩ hp
    rw [← hab, IntrinsicDivisorRatio.Intrinsic.ord_div X.carrier _ _ hfa hfb,
      Stalk.DivisorRestriction.order_of_local_element X.carrier x a ha₀ ⟨p, hprime⟩ hp,
      Stalk.DivisorRestriction.order_of_local_element X.carrier x b hb₀ ⟨p, hprime⟩ hp] at hz
    change ((Ring.ord S (algebraMap R S a)).toNat : ℤ) -
      ((Ring.ord S (algebraMap R S b)).toNat : ℤ) = 0 at hz
    have hn : (Ring.ord S (algebraMap R S b)).toNat =
        (Ring.ord S (algebraMap R S a)).toNat := by omega
    exact (ENat.natCast_toNat hnb).symm.trans
      ((congrArg (fun n : ℕ => (n : ℕ∞)) hn).trans (ENat.natCast_toNat hna))
  obtain ⟨u, hu⟩ := hass
  refine ⟨u, u.isUnit, ?_⟩
  rw [← hab, ← hu, map_mul]
  exact (mul_div_cancel_left₀ (algebraMap R K (u : R)) hfb).symm

theorem exists_unit (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (W : IrreducibleCloseds X.carrier) (f : X.carrier.functionField) (hf : f ≠ 0)
    (ho : ∀ B : X.DimensionCycleSupport 1, W ≤ B.val →
      X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = 0) :
    ∃ a : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W), IsUnit a ∧
      algebraMap (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W)) X.carrier.functionField a = f := by
  apply exists_unit_at X (CycleClass.Thom.IntersectionGeometry.supportPoint W) f hf
  intro p hp
  have hcod : X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint W) p) = 1 := by
    apply CoheightOneCodimension.codimension X m
    rw [Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
    exact hp
  let B : X.DimensionCycleSupport 1 := ⟨Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint W) p, hcod⟩
  have hWB : W ≤ B.val :=
    (Supports.supportPoint_mem_iff_subset
      (⟨(B.val : Set X.carrier), B.val.isClosed⟩ : Closeds X.carrier) W).mp
      (Stalk.DivisorSupport.point_mem_primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint W) p)
  exact (Stalk.DivisorSupport.primeClosure_point X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint W) p) ▸ ho B hWB

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AvoidingDivisorUnit
