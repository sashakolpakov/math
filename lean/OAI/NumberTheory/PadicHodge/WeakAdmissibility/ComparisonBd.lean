import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamLog

/-! # Comparison Bd -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd

noncomputable section

/-! The actual de Rham fraction field and the full crystalline comparison map. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamLog
variable (p : ℕ) [Fact p.Prime]

def deRhamDenominators : Submonoid (DeRhamDVR.DeRhamCompletion p) :=
  Submonoid.closure ((AdicCompletion.of (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p)) ''
    {a | DeRham.deRhamIdeal p = Ideal.span {a}})

instance deRham_commRing : CommRing (Logarithm.PeriodRings.BdR p) :=
  inferInstanceAs (CommRing (Localization (deRhamDenominators p)))

instance deRham_algebra : Algebra (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) :=
  inferInstanceAs (Algebra (DeRhamDVR.DeRhamCompletion p) (Localization (deRhamDenominators p)))

instance deRham_localization : IsLocalization (deRhamDenominators p) (Logarithm.PeriodRings.BdR p) :=
  inferInstanceAs (IsLocalization (deRhamDenominators p) (Localization (deRhamDenominators p)))

theorem denominator_ne_zero (a : Logarithm.PeriodRings.BInf p) (ha : DeRham.deRhamIdeal p = Ideal.span {a}) :
    AdicCompletion.of (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p) a ≠ 0 := by
  intro hz
  have ha₀ : a = 0 := (DeRhamEmbedding.bInfToBdRPlus_injective p) (hz.trans (map_zero _).symm)
  have hxi : DeRhamEmbedding.xiBInf p ∈ Ideal.span {a} := by
    rw [← ha, DeRhamEmbedding.deRhamIdeal_eq_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [ha₀, Ideal.span_singleton_zero, Ideal.mem_bot] at hxi
  apply DeRhamDVR.xiDeRham_ne_zero p
  change algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamDVR.DeRhamCompletion p) (DeRhamEmbedding.xiBInf p) = 0
  rw [hxi, map_zero]

theorem denominators_regular : deRhamDenominators p ≤ nonZeroDivisors (DeRhamDVR.DeRhamCompletion p) := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (denominator_ne_zero p a ha)

theorem deRham_algebraMap_injective :
    Function.Injective (algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p)) :=
  IsLocalization.injective (Logarithm.PeriodRings.BdR p) (denominators_regular p)

theorem xiDeRham_mem_denominators : DeRhamDVR.xiDeRham p ∈ deRhamDenominators p :=
  Submonoid.subset_closure ⟨DeRhamEmbedding.xiBInf p, DeRhamEmbedding.deRhamIdeal_eq_span p, rfl⟩

theorem xiDeRham_isUnit :
    IsUnit (algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) (DeRhamDVR.xiDeRham p)) :=
  IsLocalization.map_units (Logarithm.PeriodRings.BdR p) ⟨DeRhamDVR.xiDeRham p, xiDeRham_mem_denominators p⟩

theorem nonzero_deRham_isUnit (x : DeRhamDVR.DeRhamCompletion p) (hx : x ≠ 0) :
    IsUnit (algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) x) := by
  obtain ⟨n, u, hu⟩ := DeRhamDVR.exists_unit_factor p x hx
  rw [hu, map_mul, map_pow]
  exact ((xiDeRham_isUnit p).pow n).mul (u.isUnit.map (algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p)))

instance deRham_fractionRing : IsFractionRing (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p) :=
  IsLocalization.of_le (deRhamDenominators p) (nonZeroDivisors (DeRhamDVR.DeRhamCompletion p)) (denominators_regular p)
    (fun x hx => nonzero_deRham_isUnit p x (mem_nonZeroDivisors_iff_ne_zero.mp hx))

instance deRham_field : Field (Logarithm.PeriodRings.BdR p) := IsFractionRing.toField (DeRhamDVR.DeRhamCompletion p)

def bdRPlusToBdR : Logarithm.PeriodRings.BdRPlus p →+* Logarithm.PeriodRings.BdR p := algebraMap (DeRhamDVR.DeRhamCompletion p) (Logarithm.PeriodRings.BdR p)

theorem bdRPlusToBdR_injective : Function.Injective (bdRPlusToBdR p) :=
  deRham_algebraMap_injective p

def bCrisPlusToBdR : Logarithm.PeriodRings.BCrisPlus p →+* Logarithm.PeriodRings.BdR p :=
  (bdRPlusToBdR p).comp (Comparison.bCrisPlusToBdRPlus p)

theorem cyclotomicPeriod_deRham_isUnit :
    IsUnit (bCrisPlusToBdR p (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p))) := by
  apply isUnit_iff_ne_zero.mpr
  change bdRPlusToBdR p (Comparison.bCrisPlusToBdRPlus p
    (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p))) ≠ 0
  rw [Comparison.bCrisPlusToBdRPlus_algebraMap]
  exact (map_ne_zero_iff _ (bdRPlusToBdR_injective p)).mpr (DeRhamLog.cyclotomicPeriod_deRham_ne_zero p)

/-- The full comparison from the actual t-localized crystalline period ring. -/
def bCrisToBdR : Logarithm.PeriodRings.BCris p →+* Logarithm.PeriodRings.BdR p :=
  IsLocalization.Away.lift (g := bCrisPlusToBdR p)
    (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p))
    (cyclotomicPeriod_deRham_isUnit p)

theorem bCrisToBdR_algebraMap (x : Logarithm.PeriodRings.BCrisPlus p) :
    bCrisToBdR p (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p) x) = bCrisPlusToBdR p x := by
  unfold bCrisToBdR
  rw [IsLocalization.Away.lift_eq]

instance bCris_nontrivial : Nontrivial (Logarithm.PeriodRings.BCris p) := (bCrisToBdR p).domain_nontrivial

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd
