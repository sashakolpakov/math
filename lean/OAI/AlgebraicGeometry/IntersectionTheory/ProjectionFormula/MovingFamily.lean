import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedEndpointCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedGeometricComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient

/-! # Moving Family -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingFamily

noncomputable section

/-! A moving integral projective support and the fixed smooth source
give a concrete finite endpoint cycle. Its fixed coefficients are native
global Tor Euler characteristics, and its good fibers are equivalent. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (W : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))

def movingSupport : IrreducibleCloseds (Projective.MatrixFamily.Family.space A) :=
  Closed.ImmersionSupport.support (Parameter.Polynomial.ProjectiveSubschemeFamily.moving A (CycleClass.Geometric.GenericPoint.reducedSupportι W))

def fixedSupport : IrreducibleCloseds (Projective.MatrixFamily.Family.space A) :=
  Closed.ImmersionSupport.support (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A X.embedding)

def components : Finset (IrreducibleCloseds (Projective.MatrixFamily.Family.space A)) :=
  Finite.ClosedComponents.components (Projective.MatrixFamily.Family.space A)
    (IsolatedGeometricComponents.intersection (Projective.MatrixFamily.Family.space A)
      (movingSupport X A W) (fixedSupport X A))

def coefficient (C : IrreducibleCloseds (Projective.MatrixFamily.Family.space A)) : ℚ :=
  TotalTorCoefficient.coefficient (Projective.MatrixFamily.Family.space A)
    (movingSupport X A W) (fixedSupport X A) (CycleClass.Thom.IntersectionGeometry.supportPoint C) (X.ambientDimension + 1)

theorem contained (C : IrreducibleCloseds (Projective.MatrixFamily.Family.space A))
    (hC : C ∈ components X A W) :
    (C : Set (Projective.MatrixFamily.Family.space A)) ⊆ Set.range (Projective.FamilyOnSource.Family.toAmbient X A) := by
  have hs := Finite.ClosedComponents.subset (Projective.MatrixFamily.Family.space A)
    (IsolatedGeometricComponents.intersection (Projective.MatrixFamily.Family.space A)
      (movingSupport X A W) (fixedSupport X A)) C hC
  intro y hy
  have hm : y ∈ (fixedSupport X A : Set (Projective.MatrixFamily.Family.space A)) := (hs hy).2
  exact (Flat.ClosedSupport.support_range (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A X.embedding)) ▸ hm

def cycle (p : ℕ) (a : ℂ) : X.RationalDimensionCycle p :=
  CyclePushforward.degreeComponent X p
    (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
      (ContainedFamilyCycle.Family.cycle X A (coefficient X A W) (components X A W) a))

theorem cycle_apply (p : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (B : X.DimensionCycleSupport p) :
    cycle X A W p a B =
    ∑ C ∈ components X A W, coefficient X A W C *
      GlobalParameterSum.Weights.weight (Projective.MatrixFamily.Family.space A)
        (Projective.MatrixFamily.Family.specialization A a ha (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)))
        (Affine.ParameterFiber.germ ℂ (Projective.FamilyRegularity.IntegralFamilySupport.parameterLine A)
          (Projective.MatrixFamily.Family.specialization A a ha (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val))) a) C :=
  ContainedEndpointCoefficient.coefficient X A (coefficient X A W) (components X A W)
    (contained X A W) a ha p B

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (cycle X A W p a) (cycle X A W p b) :=
  ContainedFamilyCycle.Family.rationallyEquivalent X A (coefficient X A W) (components X A W)
    m p a b ha hb

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingFamily
