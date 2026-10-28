import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimeFactorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrderSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral

/-! # Factor Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.FactorCycle

noncomputable section

/-! The prime factors of a nonzero stalk element give its actual local
divisor cycle, with coefficients equal to the native principal-divisor orders. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient UniqueFactorizationMonoid

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier)
  [UniqueFactorizationMonoid (X.carrier.presheaf.stalk x)]

local instance : IsDomain (X.carrier.presheaf.stalk x) := X.stalk_isDomain x

def cycle (a : X.carrier.presheaf.stalk x) : X.RationalDimensionCycle 1 :=
  ((factors a).attach.map (fun r => Finsupp.single
    (PrimeFactorSupport.support X m x r.val (prime_of_factor r.val r.property)) (1 : ℚ))).sum

theorem apply_cycle (a : X.carrier.presheaf.stalk x) (B : X.DimensionCycleSupport 1) :
    cycle X m x a B = ((factors a).attach.map (fun r =>
      if B = PrimeFactorSupport.support X m x r.val (prime_of_factor r.val r.property)
        then (1 : ℚ) else 0)).sum := by
  change (Finsupp.applyAddHom B) _ = _
  rw [cycle, map_multiset_sum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  simp only [Function.comp_apply, Finsupp.applyAddHom_apply, Finsupp.single_apply, eq_comm]

theorem weighted_sum (a : X.carrier.presheaf.stalk x) (v : X.DimensionCycleSupport 1 → ℚ) :
    (cycle X m x a).sum (fun D c => c * v D) =
      ((factors a).attach.map (fun r =>
        v (PrimeFactorSupport.support X m x r.val (prime_of_factor r.val r.property)))).sum := by
  change (Finsupp.linearCombination ℚ v) (cycle X m x a) = _
  rw [cycle, map_multiset_sum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  simp only [Function.comp_apply, Finsupp.linearCombination_single, one_smul]

theorem coefficient [IsIntegral X.carrier]
    (a : X.carrier.presheaf.stalk x) (ha : a ≠ 0)
    (B : X.DimensionCycleSupport 1) (hxB : x ∈ (B.val : Set X.carrier)) :
    cycle X m x a B =
      (X.carrier.ord (algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField a)
        (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ) := by
  let R := X.carrier.presheaf.stalk x
  let : IsIntegrallyClosed R := Smooth.Normal.stalk_integrallyClosed X.structureMap x
  let p : PrimeSpectrum R := Stalk.PrimeQuotient.kernelPrime X.carrier B.val x hxB
  let S := Localization.AtPrime p.asIdeal
  have hp : p.asIdeal.height = 1 := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact CurveSupports.coheight_one X m B
  let : IsDiscreteValuationRing S := NormalDivisibility.localization_dvr R p.asIdeal hp
  have haS : algebraMap R S a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective S p.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  have ho := Stalk.DivisorRestriction.order_of_local_element X.carrier x a ha p hp
  rw [Stalk.PrimeQuotient.kernelPrime_image] at ho
  rw [apply_cycle, ho, Int.cast_natCast, FactorOrderSum.rational_factors R S (algebraMap R S) a ha haS]
  have hsum : ((factors a).map (fun r => ((Ring.ord S (algebraMap R S r)).toNat : ℚ))).sum =
      ((factors a).attach.map (fun r => ((Ring.ord S (algebraMap R S r.val)).toNat : ℚ))).sum := by
    exact congrArg Multiset.sum (Multiset.attach_map_val' (factors a)
      (fun r => ((Ring.ord S (algebraMap R S r)).toNat : ℚ))).symm
  rw [hsum]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  have hr := prime_of_factor r.val r.property
  have hgeo := PrimeFactorSupport.geometric_order X m x r.val hr B hxB
  have hlocal := Stalk.DivisorRestriction.order_of_local_element X.carrier x r.val hr.ne_zero p hp
  rw [Stalk.PrimeQuotient.kernelPrime_image] at hlocal
  have h := congrArg (fun n : ℤ => (n : ℚ)) (hlocal.symm.trans hgeo)
  simpa only [Int.cast_natCast, apply_ite, Int.cast_one, Int.cast_zero] using h.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.FactorCycle
