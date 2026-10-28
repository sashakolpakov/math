import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionExtension
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Number Field Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction

noncomputable section

/-! The native rational period space carries the full number-field
action extending the actual integral PEL action. Its field dimension is
derived from the native period rank and the degree of the field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

local instance : IsIntegral (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.left := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).variety.property

omit [NumberField E] [Algebra ℚ E] in
theorem preserves_rationalPeriods (a : NumberField.RingOfIntegers E)
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (hv : v ∈ RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :
    IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a v ∈ RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (IntegralAction.IntrinsicIntegralAction.linearAction_preserves A P ρ a v hv)
  | zero => exact (IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a).map_zero.symm ▸ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).zero_mem
  | add v w _ _ hv hw =>
      exact ((IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a).map_add v w).symm ▸
        (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).add_mem hv hw
  | smul q v _ hv =>
      exact (((IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a).restrictScalars ℚ).map_smul q v).symm ▸
        (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).smul_mem q hv

def rationalAction : NumberField.RingOfIntegers E →+*
    Module.End ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) where
  toFun a := (((IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a).restrictScalars ℚ).domRestrict
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))).codRestrict (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
      (fun v => preserves_rationalPeriods A P ρ a v.val v.property)
  map_zero' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (IntegralAction.IntrinsicIntegralAction.linearAction A P ρ).map_zero v.val
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (IntegralAction.IntrinsicIntegralAction.linearAction A P ρ).map_one v.val
  map_add' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun ((IntegralAction.IntrinsicIntegralAction.linearAction A P ρ).map_add a b) v.val
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun ((IntegralAction.IntrinsicIntegralAction.linearAction A P ρ).map_mul a b) v.val

def fieldAction : E →ₐ[ℚ] Module.End ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
  Integral.ActionExtension.extendIntegralAction (E := E) (D := Module.End ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))) (rationalAction A P ρ)

theorem fieldAction_integer_apply (a : NumberField.RingOfIntegers E)
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :
    fieldAction A P ρ (a : E) v = rationalAction A P ρ a v := by
  exact Integral.ActionExtension.extendIntegralAction_end_apply (rationalAction A P ρ) a v

abbrev fieldModule : Module E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
  Module.compHom (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (fieldAction A P ρ).toRingHom

abbrev fieldScalarTower : let := fieldModule A P ρ
    IsScalarTower ℚ E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) := by
  let := fieldModule A P ρ
  refine ⟨fun q a v => ?_⟩
  change fieldAction A P ρ (q • a) v = q • fieldAction A P ρ a v
  exact LinearMap.congr_fun ((fieldAction A P ρ).toLinearMap.map_smul q a) v

/-- A dimension-3s abelian variety with a degree-2s field action has
a native rational period space of dimension three over that field. -/
theorem field_finrank_three (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) :
    let := fieldModule A P ρ
    Module.finrank E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) = 3 := by
  let := fieldModule A P ρ
  let := fieldScalarTower A P ρ
  let : Module.Finite E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
    Module.Finite.of_restrictScalars_finite ℚ E _
  have h := Module.finrank_mul_finrank ℚ E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
  rw [hdegree, RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank] at h
  have hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.hom = g :=
    Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A
  have h' := h.trans (congrArg (fun n : ℕ => 2 * n) (hd.trans hg))
  nlinarith

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction
