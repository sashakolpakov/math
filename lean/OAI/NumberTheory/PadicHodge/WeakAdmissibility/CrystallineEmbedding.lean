import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonKernel
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.InvariantComparison

/-! # Crystalline Embedding -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.CrystallineEmbedding

noncomputable section

/-! Injectivity of the actual full crystalline comparison and its invariant tensor map. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD OAI.NumberTheory.PadicHodge.WeakAdmissibility.InvariantComparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR
variable (p : ℕ) [Fact p.Prime]

theorem bCrisPlusToBdRPlus_injective : Function.Injective (Comparison.bCrisPlusToBdRPlus p) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers (p : Logarithm.PeriodRings.ACris p))
  intro a ha
  rw [Comparison.bCrisPlusToBdRPlus_algebraMap] at ha
  have hz := ComparisonKernel.aCrisToBdRPlus_injective p (ha.trans (map_zero _).symm)
  rw [hz, map_zero]

theorem bCrisPlusToBdR_injective : Function.Injective (ComparisonBd.bCrisPlusToBdR p) :=
  (ComparisonBd.bdRPlusToBdR_injective p).comp (bCrisPlusToBdRPlus_injective p)

theorem bCrisToBdR_injective : Function.Injective (ComparisonBd.bCrisToBdR p) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p)))
  intro a ha
  rw [ComparisonBd.bCrisToBdR_algebraMap] at ha
  have hz := bCrisPlusToBdR_injective p (ha.trans (map_zero _).symm)
  rw [hz, map_zero]

theorem aCrisToBCris_injective :
    Function.Injective ((algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)).comp (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p))) := by
  intro x y hxy
  apply ComparisonKernel.aCrisToBdRPlus_injective p
  apply ComparisonBd.bdRPlusToBdR_injective p
  have he := congrArg (ComparisonBd.bCrisToBdR p) hxy
  simp only [RingHom.comp_apply, ComparisonBd.bCrisToBdR_algebraMap, ComparisonBd.bCrisPlusToBdR,
    Comparison.bCrisPlusToBdRPlus_algebraMap] at he
  exact he

instance aCris_isDomain : IsDomain (Logarithm.PeriodRings.ACris p) :=
  Function.Injective.isDomain ((ComparisonBd.bdRPlusToBdR p).comp (Comparison.aCrisToBdRPlus p))
    ((ComparisonBd.bdRPlusToBdR_injective p).comp (ComparisonKernel.aCrisToBdRPlus_injective p))

instance bCrisPlus_isDomain : IsDomain (Logarithm.PeriodRings.BCrisPlus p) :=
  Function.Injective.isDomain (ComparisonBd.bCrisPlusToBdR p) (bCrisPlusToBdR_injective p)

instance bCris_isDomain : IsDomain (Logarithm.PeriodRings.BCris p) :=
  Function.Injective.isDomain (ComparisonBd.bCrisToBdR p) (bCrisToBdR_injective p)

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

theorem tensorComparison_injective : Function.Injective (InvariantComparison.tensorComparison p (V := V)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (bCrisToBdR_injective p) Function.injective_id

theorem invariantComparison_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ρ : Representation ℚ_[p] K.fixingSubgroup V) : Function.Injective (InvariantComparison.invariantComparison p K ρ) := by
  intro x y hxy
  apply Subtype.ext
  apply tensorComparison_injective p
  exact congrArg Subtype.val hxy

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.CrystallineEmbedding
