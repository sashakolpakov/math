import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.DivisorNorm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition

/-! # Pushforward -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Pushforward

noncomputable section

/-! Proper pushforward of ThomClass's actual principal cycle generators in the
dimension-preserving case. The result is the principal cycle of the
function-field norm on the actual closed image support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
  CyclePushforward Affine.DivisorNorm

theorem supportPrincipalDivisor_norm {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CyclePushforward.pointPushforward (Support.Map.supportImageMap f W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g) =
      Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)) (Support.Fields.supportNorm f W hdim g) := by
  let := (Support.Fields.supportFunctionFieldMap f W).hom.toAlgebra
  exact Proper.DivisorNorm.principalDivisor_norm (Support.Map.supportImageMap f W)
    (Support.Map.supportImageMap_genericPoint f W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap)
    (Support.Fields.supportFunctionField_finite f W hdim) g hg

/-- The cycle-level formula in precisely ProjectionFormula's codimension grading. -/
theorem principalCycle_pushforward_norm {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (m n p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hdeg : p + n = q + m) (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    ProperCycleLinearity.cyclePushforward f p q (ClosedSectionCycle.principalCycle X p W g) =
      ClosedSectionCycle.principalCycle Y q (ProperCycleLinearity.imageSupport f W) (Support.Fields.supportNorm f W hdim g) := by
  rw [ClosedSectionCycle.principalCycle_eq_pushforward, PushforwardComposition.Grading.cyclePushforward_degreeComponent f m n p q hdeg]
  change CyclePushforward.degreeComponent Y q (CyclePushforward.pointPushforward (Support.Map.algebraicMap f)
    (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g))) = _
  have hs := DFunLike.congr_fun (Support.Map.pointPushforward_supportImageMap f W)
    (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)
  change CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))
      (CyclePushforward.pointPushforward (Support.Map.supportImageMap f W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) =
    CyclePushforward.pointPushforward (Support.Map.algebraicMap f)
      (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) at hs
  rw [← hs, supportPrincipalDivisor_norm f W hdim g hg]
  exact (ClosedSectionCycle.principalCycle_eq_pushforward Y q (ProperCycleLinearity.imageSupport f W) (Support.Fields.supportNorm f W hdim g)).symm

/-- In the dimension-preserving case, every actual principal generator
pushes to an actual principal generator and hence to rational equivalence. -/
theorem principalCycle_pushforward_mem_of_dimension_eq {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (m n p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hdeg : p + n = q + m) (W : IrreducibleCloseds X.carrier)
    (hW : X.supportCodimension W + 1 = p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    ProperCycleLinearity.cyclePushforward f p q (ClosedSectionCycle.principalCycle X p W g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q := by
  have hY : Y.supportCodimension (ProperCycleLinearity.imageSupport f W) + 1 = q := by
    have hx := Grading.supportDimension_add_codimension X m W
    have hy := Grading.supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f W)
    omega
  rw [principalCycle_pushforward_norm f m n p q hdeg W hdim g hg]
  exact Submodule.subset_span (ClosedSectionCycle.principalCycle_isPrincipalDivisor Y q (ProperCycleLinearity.imageSupport f W) hY
    (Support.Fields.supportNorm f W hdim g) (Support.Fields.supportNorm_ne_zero f W hdim g hg))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Pushforward
