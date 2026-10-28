import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Equivalence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneHilbert

/-! # Anti One Source Pair -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern

/-! The actual antiholomorphic one-form Hilbert space with any constructed Hermitian metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def HolomorphicMetric.Data.HolomorphicLineMetricData.antiOneL2Submodule : Submodule ℂ (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1) :=
  (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Submodule V u).comap (HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1).toLinearMap

abbrev Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With := h.antiOneL2Submodule V

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.antiOneL2Submodule_isClosed :
    IsClosed (h.antiOneL2Submodule V : Set (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1)) := by
  have hc : IsClosed (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Submodule V u : Set (Holomorphic.FormCompletion.HolomorphicFormL2 V u 1)) :=
    (Holomorphic.AntiOneHilbert.holomorphicL2OnePart V u - ContinuousLinearMap.id ℂ (Holomorphic.FormCompletion.HolomorphicFormL2 V u 1)).isClosed_ker
  exact hc.preimage (HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1).continuous

instance Holomorphic.AntiOneSourcePair.holomorphicAntiOneL2With_completeSpace : CompleteSpace (Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :=
  (h.antiOneL2Submodule_isClosed V).completeSpace_coe

def Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h ≃L[ℂ] Holomorphic.AntiOneHilbert.HolomorphicAntiOneL2 V u :=
  (HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1).ofSubmodule' (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Submodule V u)

theorem Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv_val (a : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h a).val = HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1 a.val := rfl

def Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).symm.toLinearMap.comp (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Inclusion V u)

theorem Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a).val = Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 a.val := by
  change (HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1).symm (Holomorphic.FormCompletion.holomorphicFormL2Inclusion V u 1 a.val) = _
  exact (HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1).symm_apply_eq.mpr
    (HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv_inclusion V h 1 a.val).symm

theorem Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) =
      Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Inclusion V u a :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).apply_symm_apply (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Inclusion V u a)

theorem Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_injective : Function.Injective (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h) :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).symm.injective.comp (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Inclusion_injective V u)

theorem Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_dense : DenseRange (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h) :=
  (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).symm.surjective.denseRange.comp
    (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Inclusion_dense V u) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneEquiv V h).symm.continuous

theorem Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_inner (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b) =
      h.formIntegralPair V 1 a.val b.val := by
  change inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a).val (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b).val = _
  exact (congrArg₂ (inner ℂ : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 → Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 → ℂ)
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h a) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h b)).trans
      (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 1 a.val b.val)

end AlgebraicGeometry.DivisorClass.Chern

namespace AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneSourcePair

/-! The original antiholomorphic Hilbert pairing with a smooth test agrees exactly with its ambient bundle L² pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicMetricAntiOneInclusion_source_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (v : HolomorphicAntiOneL2With V h) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ v (holomorphicMetricAntiOneInclusion V h a) =
      inner ℂ ((h.antiOneL2Submodule V).subtypeL v) (IntegralPairZero.holomorphicFormL2WithInclusion V h 1 a.val) :=
  congrArg (fun b : IntegralPairZero.HolomorphicFormL2With V h 1 => inner ℂ ((h.antiOneL2Submodule V).subtypeL v) b)
    (holomorphicMetricAntiOneInclusion_val V h a)

end AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneSourcePair

end

end OAI
