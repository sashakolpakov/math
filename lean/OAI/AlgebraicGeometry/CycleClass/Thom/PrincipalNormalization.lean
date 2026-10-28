import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Pushforward
import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry

/-! # Principal Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalNormalization.Constructions

noncomputable section

/-! The normalization divisor formula in the exact coefficient convention
used by ThomClass's principal-divisor rational-equivalence generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PushforwardFiber.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions
  Normalization.Scheme.Constructions Normalization.Fields.Constructions Normalization.Field.Constructions
  NormalizationDivisor.Pushforward.Constructions.Local

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (W : IrreducibleCloseds X.carrier)

/-- Closed-support pushforward gives exactly the principal-divisor coefficient
in the faithful definition, including coefficients outside the support. -/
theorem principalDivisorCoefficient_eq_pointPushforward
    (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (C : IrreducibleCloseds X.carrier) :
    Point.Constructions.pointPushforward (Geometric.GenericPoint.reducedSupportι W)
      (Point.Constructions.rationalPrincipalPointDivisor (Geometric.GenericPoint.reducedSupportScheme W) g) (IntersectionGeometry.supportPoint C) =
        IntersectionGeometry.principalDivisorCoefficient X W g C := by
  by_cases h : IntersectionGeometry.supportPoint C ∈ (W : Set X.carrier)
  · let x := IntersectionGeometry.supportPreimage W (IntersectionGeometry.supportPoint C) h
    have hx : Geometric.GenericPoint.reducedSupportι W x = IntersectionGeometry.supportPoint C :=
      IntersectionGeometry.supportPreimage_spec W (IntersectionGeometry.supportPoint C) h
    rw [PushforwardFiber.Constructions.pointPushforward_uniqueFiber (Geometric.GenericPoint.reducedSupportι W) x (IntersectionGeometry.supportPoint C) hx
      (fun y hy => (Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective (hy.trans hx.symm)),
      ResidueDegree.Constructions.residueDegree_immersion, Nat.cast_one, mul_one]
    exact (IntersectionGeometry.principalDivisorCoefficient_at_image X W g C x hx).symm
  · rw [IntersectionGeometry.principalDivisorCoefficient, dite_eq_right h]
    apply PushforwardFiber.Constructions.pointPushforward_apply_eq_zero
    intro y _ hy
    apply h
    rw [← Geometric.GenericPoint.range_reducedSupportι W]
    exact ⟨y, hy⟩

/-- Normalization recovers the exact ThomClass coefficient with its actual finite
morphism and actual pulled-back function, without a smoothness assumption. -/
theorem principalDivisorCoefficient_eq_normalizationPushforward
    (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (C : IrreducibleCloseds X.carrier) :
    letI := Normalization.Field.Constructions.finiteNormalization_noetherian (Geometric.GenericPoint.reducedSupportScheme W)
      (Geometric.SupportFiniteType.supportStructureMap W X.structureMap)
    Point.Constructions.pointPushforward (Normalization.Scheme.Constructions.normalizationMap (Geometric.GenericPoint.reducedSupportScheme W) ≫ Geometric.GenericPoint.reducedSupportι W)
      (Point.Constructions.rationalPrincipalPointDivisor (Normalization.Scheme.Constructions.normalization (Geometric.GenericPoint.reducedSupportScheme W))
        ((Normalization.Fields.Constructions.normalizationFieldIso (Geometric.GenericPoint.reducedSupportScheme W)).hom g)) (IntersectionGeometry.supportPoint C) =
          IntersectionGeometry.principalDivisorCoefficient X W g C := by
  let := Normalization.Field.Constructions.finiteNormalization_noetherian (Geometric.GenericPoint.reducedSupportScheme W)
    (Geometric.SupportFiniteType.supportStructureMap W X.structureMap)
  rw [Point.Constructions.pointPushforward_comp, LinearMap.comp_apply,
    NormalizationDivisor.Pushforward.Constructions.Local.normalizationPrincipalDivisor_pushforward (Geometric.GenericPoint.reducedSupportScheme W)
      (Geometric.SupportFiniteType.supportStructureMap W X.structureMap) g hg]
  exact principalDivisorCoefficient_eq_pointPushforward X W g C

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalNormalization.Constructions
