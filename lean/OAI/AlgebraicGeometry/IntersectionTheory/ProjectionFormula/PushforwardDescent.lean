import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PrincipalDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Pushforward
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DimensionDrop

/-! # Pushforward Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardDescent

noncomputable section

/-! Proper pushforward descends unconditionally through ThomClass's actual
rational equivalence. Equal-dimensional supports use the field norm;
dimension loss one uses relative principal-divisor degree zero; larger
loss is killed by the grading. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

theorem principalCycle_pushforward_eq_zero_of_dimension_one
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (m n p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (hdeg : p + n = q + m)
    (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    ProperCycleLinearity.cyclePushforward f p q (Principal.ClosedSectionCycle.principalCycle X p W g) = 0 := by
  let : IsProper X.structureMap := X.projective.isProper
  let : IsProper Y.structureMap := Y.projective.isProper
  let : Foundations.Scheme.ProjectiveSpace.complexBase.IsSeparated := by
    change (Spec (.of ℂ)).IsSeparated
    infer_instance
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (CycleClass.Geometric.SupportFiniteType.supportStructureMap W X.structureMap)]
    dsimp only [CycleClass.Geometric.SupportFiniteType.supportStructureMap]
    infer_instance⟩
  let : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap)]
    dsimp only [CycleClass.Geometric.SupportFiniteType.supportStructureMap]
    infer_instance⟩
  have hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap) + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Support.Map.supportImageMap f W ≫
        CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap) := by
    rw [Support.Map.supportImageMap_over]
    exact hdim
  have hz := Relative.PrincipalDivisor.pushforward_eq_zero (Support.Map.supportImageMap f W)
    (Support.Map.supportImageMap_genericPoint f W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap) hd g hg
  rw [Principal.ClosedSectionCycle.principalCycle_eq_pushforward,
    PushforwardComposition.Grading.cyclePushforward_degreeComponent f m n p q hdeg]
  change CyclePushforward.degreeComponent Y q (CyclePushforward.pointPushforward (Support.Map.algebraicMap f)
    (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g))) = 0
  have hs := DFunLike.congr_fun (Support.Map.pointPushforward_supportImageMap f W)
    (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)
  change CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))
      (CyclePushforward.pointPushforward (Support.Map.supportImageMap f W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) =
    CyclePushforward.pointPushforward (Support.Map.algebraicMap f)
      (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) at hs
  rw [← hs, hz, map_zero, map_zero]

theorem principalCycle_pushforward_mem
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (m n p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (hdeg : p + n = q + m)
    (W : IrreducibleCloseds X.carrier) (hW : X.supportCodimension W + 1 = p)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    ProperCycleLinearity.cyclePushforward f p q (Principal.ClosedSectionCycle.principalCycle X p W g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y q := by
  have hle : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap := by
    have h := Cycles.Functoriality.FunctionFields.Construction.dimension_le_of_genericPoint (Support.Map.supportImageMap f W)
      (Support.Map.supportImageMap_genericPoint f W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap)
    rw [Support.Map.supportImageMap_over] at h
    exact h
  by_cases heq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap
  · exact Principal.Pushforward.principalCycle_pushforward_mem_of_dimension_eq
      f m n p q hdeg W hW heq g hg
  by_cases hone : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap
  · rw [principalCycle_pushforward_eq_zero_of_dimension_one f m n p q hdeg W hone g hg]
    exact Submodule.zero_mem _
  · rw [DimensionDrop.principalCycle_pushforward_eq_zero_of_dimension_drop
      f m n p q hdeg W hW g (by omega)]
    exact Submodule.zero_mem _

theorem chowPushforward_map_exists
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (m n p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (hdeg : p + n = q + m) :
    ∃ F : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ Y q, ∀ a, ProperCycleLinearity.chowPushforward f p q a = {F a} := by
  apply (ProperCycleLinearity.chowPushforward_map_exists_iff f p q).mpr
  intro z hz
  obtain ⟨W, hW, g, hg, rfl⟩ := (Principal.ClosedSectionCycle.isPrincipalDivisor_iff X p z).mp hz
  exact principalCycle_pushforward_mem f m n p q hdeg W hW g hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardDescent
