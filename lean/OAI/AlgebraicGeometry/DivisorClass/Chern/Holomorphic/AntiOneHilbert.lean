import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Projection
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Anti One Hilbert -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneHilbert

noncomputable section

section

/-! A genuine continuous type projection on the native Hilbert completion of bundle one-forms. -/

open _root_.TopologicalSpace UniformSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicMetricOnePart : FormCompletion.HolomorphicMetricForm V u 1 →ₗ[ℂ] FormCompletion.HolomorphicMetricForm V u 1 where
  toFun a := ⟨OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a.val⟩
  map_add' a b := congrArg OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk ((OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I).map_add a.val b.val)
  map_smul' z a := congrArg OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk ((OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I).map_smul z a.val)

theorem holomorphicMetricOnePart_norm (a : FormCompletion.HolomorphicMetricForm V u 1) :
    ‖holomorphicMetricOnePart V u a‖ ≤ ‖a‖ := by
  have h := HolomorphicMetric.Projection.holomorphicLineOnePart_norm V u a.val
  change ‖((holomorphicMetricOnePart V u a : FormCompletion.HolomorphicMetricForm V u 1) : FormCompletion.HolomorphicFormL2 V u 1)‖ ≤
    ‖((a : FormCompletion.HolomorphicMetricForm V u 1) : FormCompletion.HolomorphicFormL2 V u 1)‖ at h
  simpa only [Completion.norm_coe] using h

def holomorphicMetricOnePartCLM : FormCompletion.HolomorphicMetricForm V u 1 →L[ℂ] FormCompletion.HolomorphicMetricForm V u 1 :=
  (holomorphicMetricOnePart V u).mkContinuous 1 (fun a => by
    simpa only [one_mul] using holomorphicMetricOnePart_norm V u a)

def holomorphicL2OnePart : FormCompletion.HolomorphicFormL2 V u 1 →L[ℂ] FormCompletion.HolomorphicFormL2 V u 1 :=
  ((Completion.toComplL : FormCompletion.HolomorphicMetricForm V u 1 →L[ℂ] FormCompletion.HolomorphicFormL2 V u 1).comp
    (holomorphicMetricOnePartCLM V u)).extend
      (Completion.toComplL : FormCompletion.HolomorphicMetricForm V u 1 →L[ℂ] FormCompletion.HolomorphicFormL2 V u 1)

theorem holomorphicL2OnePart_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    holomorphicL2OnePart V u (FormCompletion.holomorphicFormL2Inclusion V u 1 a) =
      FormCompletion.holomorphicFormL2Inclusion V u 1 (OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a) := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
    (Completion.isUniformInducing_coe (FormCompletion.HolomorphicMetricForm V u 1)) (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk a)

theorem holomorphicL2OnePart_inclusion_inner (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℂ (holomorphicL2OnePart V u (FormCompletion.holomorphicFormL2Inclusion V u 1 a))
      (FormCompletion.holomorphicFormL2Inclusion V u 1 b) =
        inner ℂ (FormCompletion.holomorphicFormL2Inclusion V u 1 a)
          (holomorphicL2OnePart V u (FormCompletion.holomorphicFormL2Inclusion V u 1 b)) := by
  calc
    _ = inner ℂ (FormCompletion.holomorphicFormL2Inclusion V u 1 (OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a))
        (FormCompletion.holomorphicFormL2Inclusion V u 1 b) :=
      congrArg (fun z : FormCompletion.HolomorphicFormL2 V u 1 => inner ℂ z (FormCompletion.holomorphicFormL2Inclusion V u 1 b))
        (holomorphicL2OnePart_inclusion V u a)
    _ = FormIntegralPair.holomorphicLineFormIntegralPair V u 1 (OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I a) b :=
      FormCompletion.holomorphicFormL2Inclusion_inner V u 1 _ _
    _ = FormIntegralPair.holomorphicLineFormIntegralPair V u 1 a (OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I b) :=
      HolomorphicMetric.Projection.holomorphicLineOnePart_integral_pair V u a b
    _ = inner ℂ (FormCompletion.holomorphicFormL2Inclusion V u 1 a)
        (FormCompletion.holomorphicFormL2Inclusion V u 1 (OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I b)) :=
      (FormCompletion.holomorphicFormL2Inclusion_inner V u 1 _ _).symm
    _ = _ := congrArg (fun z : FormCompletion.HolomorphicFormL2 V u 1 => inner ℂ (FormCompletion.holomorphicFormL2Inclusion V u 1 a) z)
      (holomorphicL2OnePart_inclusion V u b).symm

theorem holomorphicL2OnePart_norm (a : FormCompletion.HolomorphicFormL2 V u 1) : ‖holomorphicL2OnePart V u a‖ ≤ ‖a‖ := by
  refine (FormCompletion.holomorphicFormL2Inclusion_dense V u 1).induction_on a ?_ ?_
  · exact isClosed_le (holomorphicL2OnePart V u).continuous.norm continuous_norm
  · intro b
    rw [holomorphicL2OnePart_inclusion]
    exact HolomorphicMetric.Projection.holomorphicLineOnePart_norm V u b

theorem holomorphicL2OnePart_idempotent (a : FormCompletion.HolomorphicFormL2 V u 1) :
    holomorphicL2OnePart V u (holomorphicL2OnePart V u a) = holomorphicL2OnePart V u a := by
  refine (FormCompletion.holomorphicFormL2Inclusion_dense V u 1).induction_on a ?_ ?_
  · exact isClosed_eq ((holomorphicL2OnePart V u).continuous.comp (holomorphicL2OnePart V u).continuous)
      (holomorphicL2OnePart V u).continuous
  · intro b
    rw [holomorphicL2OnePart_inclusion, holomorphicL2OnePart_inclusion, OneFormProjection.holomorphicLineOnePart_idempotent]

theorem holomorphicL2OnePart_selfAdjoint (a b : FormCompletion.HolomorphicFormL2 V u 1) :
    inner ℂ (holomorphicL2OnePart V u a) b = inner ℂ a (holomorphicL2OnePart V u b) := by
  refine (FormCompletion.holomorphicFormL2Inclusion_dense V u 1).induction_on a ?_ ?_
  · exact isClosed_eq ((holomorphicL2OnePart V u).continuous.inner continuous_const)
      (continuous_id.inner ((holomorphicL2OnePart V u).continuous.comp continuous_const))
  · intro c
    refine (FormCompletion.holomorphicFormL2Inclusion_dense V u 1).induction_on b ?_ ?_
    · exact isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner (holomorphicL2OnePart V u).continuous)
    · intro d
      exact holomorphicL2OnePart_inclusion_inner V u c d

end

/-! The closed Hilbert space of actual antiholomorphic bundle one-forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicAntiOneL2Submodule : Submodule ℂ (FormCompletion.HolomorphicFormL2 V u 1) :=
  (holomorphicL2OnePart V u - ContinuousLinearMap.id ℂ (FormCompletion.HolomorphicFormL2 V u 1)).ker

abbrev HolomorphicAntiOneL2 := holomorphicAntiOneL2Submodule V u

theorem holomorphicAntiOneL2_mem (a : FormCompletion.HolomorphicFormL2 V u 1) :
    a ∈ holomorphicAntiOneL2Submodule V u ↔ holomorphicL2OnePart V u a = a := by
  change holomorphicL2OnePart V u a - a = 0 ↔ _
  exact sub_eq_zero

instance holomorphicAntiOneL2_completeSpace : CompleteSpace (HolomorphicAntiOneL2 V u) :=
  inferInstanceAs (CompleteSpace
    (holomorphicL2OnePart V u - ContinuousLinearMap.id ℂ (FormCompletion.HolomorphicFormL2 V u 1)).ker)

def holomorphicL2ToAntiOne : FormCompletion.HolomorphicFormL2 V u 1 →L[ℂ] HolomorphicAntiOneL2 V u :=
  (holomorphicL2OnePart V u).codRestrict _ fun a =>
    (holomorphicAntiOneL2_mem V u _).mpr (holomorphicL2OnePart_idempotent V u a)

theorem holomorphicL2ToAntiOne_surjective : Function.Surjective (holomorphicL2ToAntiOne V u) := by
  intro a
  refine ⟨a.val, ?_⟩
  apply Subtype.ext
  exact (holomorphicAntiOneL2_mem V u a.val).mp a.property

theorem holomorphicL2OnePart_anti_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    holomorphicL2OnePart V u (FormCompletion.holomorphicFormL2Inclusion V u 1 a.val) =
      FormCompletion.holomorphicFormL2Inclusion V u 1 a.val :=
  (holomorphicL2OnePart_inclusion V u a.val).trans
    (congrArg (FormCompletion.holomorphicFormL2Inclusion V u 1) (OneFormProjection.holomorphicLineOnePart_eq_of_anti u ⊤ a.val a.property))

def holomorphicAntiOneL2Inclusion : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] HolomorphicAntiOneL2 V u :=
  ((FormCompletion.holomorphicFormL2Inclusion V u 1).comp (HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1).subtype).codRestrict _
    fun a => (holomorphicAntiOneL2_mem V u _).mpr (holomorphicL2OnePart_anti_inclusion V u a)

theorem holomorphicAntiOneL2Inclusion_val (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    (holomorphicAntiOneL2Inclusion V u a).val = FormCompletion.holomorphicFormL2Inclusion V u 1 a.val := rfl

theorem holomorphicAntiOneL2Inclusion_injective : Function.Injective (holomorphicAntiOneL2Inclusion V u) := by
  intro a b h
  apply Subtype.ext
  apply FormCompletion.holomorphicFormL2Inclusion_injective V u 1
  exact congrArg Subtype.val h

theorem holomorphicL2ToAntiOne_inclusion (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    holomorphicL2ToAntiOne V u (FormCompletion.holomorphicFormL2Inclusion V u 1 a) =
      holomorphicAntiOneL2Inclusion V u (OneFormProjection.holomorphicLineOneAntiProjection u ⊤ a) := by
  apply Subtype.ext
  exact holomorphicL2OnePart_inclusion V u a

theorem holomorphicAntiOneL2Inclusion_dense : DenseRange (holomorphicAntiOneL2Inclusion V u) := by
  have hd := (holomorphicL2ToAntiOne_surjective V u).denseRange.comp
    (FormCompletion.holomorphicFormL2Inclusion_dense V u 1) (holomorphicL2ToAntiOne V u).continuous
  apply hd.mono
  rintro _ ⟨a, rfl⟩
  exact ⟨OneFormProjection.holomorphicLineOneAntiProjection u ⊤ a, (holomorphicL2ToAntiOne_inclusion V u a).symm⟩

theorem holomorphicAntiOneL2Inclusion_inner (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ (holomorphicAntiOneL2Inclusion V u a) (holomorphicAntiOneL2Inclusion V u b) =
      FormIntegralPair.holomorphicLineFormIntegralPair V u 1 a.val b.val :=
  FormCompletion.holomorphicFormL2Inclusion_inner V u 1 a.val b.val

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneHilbert
