import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointMultiplicity

/-! # Moving Zero Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingZeroCoefficient

noncomputable section

/-! At zero, the rationally equivalent moving-family cycle has
the exact native ThomClass intersection multiplicity of the original support
and X whenever their intersection has the specified proper codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial.ProjectiveSubschemeFamily

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (W : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))

theorem coefficient (p d : ℕ)
    (hproper : ∀ D : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension),
      (D : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ⊆ (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ∩
        Set.range X.embedding → d ≤ (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension D)
    (B : X.DimensionCycleSupport p)
    (D : (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).DimensionCycleSupport d)
    (hD : CycleClass.Thom.IntersectionGeometry.supportPoint D.val = X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val))
    (hW : X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) ∈ (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) :
    MovingFamily.Family.cycle X A W p 0 B =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Projective.Dimension.SpacePresentation.presentation X.ambientDimension)
        W (Closed.ImmersionSupport.support X.embedding) D.val := by
  let hz := Polynomial.MatrixPath.zero_good A
  have ht₁ : Parameter.Polynomial.ProjectiveSubschemeFamily.moving A (CycleClass.Geometric.GenericPoint.reducedSupportι W) ≫ Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A =
      Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A (CycleClass.Geometric.GenericPoint.reducedSupportι W) ≫ Parameter.Polynomial.IntegralProduct.toLine A := by
    rw [Projective.FamilyRegularity.IntegralFamilySupport.parameterLine, ← Category.assoc, Parameter.Polynomial.ProjectiveSubschemeFamily.moving_parameter]
  have ht₂ : Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A X.embedding ≫ Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A =
      Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A X.embedding ≫ Parameter.Polynomial.IntegralProduct.toLine A := by
    exact (Category.assoc _ _ _).symm
  have hp : ∀ C : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension),
      (C : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ⊆
        (Projective.MatrixFamily.Family.specialization A 0 hz ⁻¹'
          (Closed.ImmersionSupport.support (Parameter.Polynomial.ProjectiveSubschemeFamily.moving A (CycleClass.Geometric.GenericPoint.reducedSupportι W)) : Set (Projective.MatrixFamily.Family.space A))) ∩
        (Projective.MatrixFamily.Family.specialization A 0 hz ⁻¹'
          (Closed.ImmersionSupport.support (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A X.embedding) : Set (Projective.MatrixFamily.Family.space A))) →
        d ≤ (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension C := by
    intro C hC
    change (C : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ⊆
      (Projective.MatrixFamily.Family.specialization A 0 hz ⁻¹'
        (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A))) ∩
      (Projective.MatrixFamily.Family.specialization A 0 hz ⁻¹'
        (MovingFamily.Family.fixedSupport X A : Set (Projective.MatrixFamily.Family.space A))) at hC
    rw [MovingSupport.zero_moving, MovingSupport.fixed_slice] at hC
    exact hproper C hC
  have hx₁ : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈
      (Closed.ImmersionSupport.support (CycleClass.Geometric.GenericPoint.reducedSupportι W) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) := by
    rw [MovingSupport.reduced_image, hD]
    exact hW
  have hx₂ : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈
      (Closed.ImmersionSupport.support X.embedding : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) := by
    rw [Flat.ClosedSupport.support_range, hD]
    exact ⟨CycleClass.Thom.IntersectionGeometry.supportPoint B.val, rfl⟩
  have hs := Projective.EndpointMultiplicity.global_sum A (CycleClass.Geometric.GenericPoint.reducedSupportι W) X.embedding 0 hz
    (CycleClass.Geometric.GenericPoint.reducedSupportι W) X.embedding (Parameter.Polynomial.ProjectiveSubschemeFamily.moving A (CycleClass.Geometric.GenericPoint.reducedSupportι W)) (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A X.embedding)
    (Parameter.Polynomial.ProjectiveSubschemeFamily.moving_zero A (CycleClass.Geometric.GenericPoint.reducedSupportι W)).symm (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization_ambient A X.embedding 0 hz).symm
    ht₁ ht₂ d hp D hx₁ hx₂
  rw [MovingSupport.reduced_image] at hs
  rw [hD] at hs
  exact (MovingFamily.Family.cycle_apply X A W p 0 hz B).trans hs.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingZeroCoefficient
