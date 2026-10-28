import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingFamily
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport

/-! # Moving Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingSupport

noncomputable section

/-! The native moving intersection cycle is supported on its actual
marked intersection, whose zero and one slices are the original and
translated projective supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem reduced_image (Z : Scheme) (C : IrreducibleCloseds Z) :
    Closed.ImmersionSupport.support (CycleClass.Geometric.GenericPoint.reducedSupportι C) = C := by
  apply IrreducibleCloseds.ext
  rw [Flat.ClosedSupport.support_range, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (W : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))

omit [IsIntegral X.carrier] in
theorem moving_coe : (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A)) =
    (Projective.FamilySupport.Family.support A ⟨(W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)), W.isClosed⟩ :
      Set (Projective.MatrixFamily.Family.space A)) := by
  have h := Projective.FamilyRegularity.IntegralFamilySupport.support_eq A (CycleClass.Geometric.GenericPoint.reducedSupportι W)
  rw [reduced_image] at h
  exact h

theorem fixed_coe : (MovingFamily.Family.fixedSupport X A : Set (Projective.MatrixFamily.Family.space A)) =
    Projective.FamilySupport.Family.projection A ⁻¹' Set.range X.embedding := by
  change (Closed.ImmersionSupport.support (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A X.embedding) :
    Set (Projective.MatrixFamily.Family.space A)) = _
  rw [Flat.ClosedSupport.support_range]
  exact Scheme.Pullback.range_fst _ _

omit [IsIntegral X.carrier] in
theorem zero_moving : Projective.MatrixFamily.Family.specialization A 0 (Polynomial.MatrixPath.zero_good A) ⁻¹'
    (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A)) =
      (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) := by
  rw [moving_coe, Projective.FamilySupport.Family.zero_slice]
  rfl

omit [IsIntegral X.carrier] in
theorem one_moving : Projective.MatrixFamily.Family.specialization A 1 (Polynomial.MatrixPath.one_good A) ⁻¹'
    (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A)) =
      Projective.LinearChart.Automorphism.map A '' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) := by
  rw [moving_coe, Projective.FamilySupport.Family.one_slice]
  rfl

theorem fixed_slice (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    Projective.MatrixFamily.Family.specialization A a ha ⁻¹'
      (MovingFamily.Family.fixedSupport X A : Set (Projective.MatrixFamily.Family.space A)) =
      Set.range X.embedding := by
  rw [fixed_coe]
  change (Projective.MatrixFamily.Family.specialization A a ha ≫ Projective.FamilySupport.Family.projection A) ⁻¹'
    Set.range X.embedding = _
  rw [Projective.FamilySupport.Family.specialization_projection]
  rfl

def intersection (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) : Closeds X.carrier :=
  ⟨(X.embedding ≫ Projective.MatrixFamily.Family.specialization A a ha) ⁻¹'
      (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A)),
    (MovingFamily.Family.movingSupport X A W).isClosed.preimage
      (X.embedding ≫ Projective.MatrixFamily.Family.specialization A a ha).continuous⟩

theorem supported (p : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    CycleSupport.SupportedOn X p (MovingFamily.Family.cycle X A W p a)
      (intersection X A W a ha) := by
  intro B hB
  apply (Supports.supportPoint_mem_iff_subset (intersection X A W a ha) B.val).mp
  by_contra hn
  have hc := Finsupp.mem_support_iff.mp hB
  apply hc
  rw [MovingFamily.Family.cycle_apply X A W p a ha B]
  apply Finset.sum_eq_zero
  intro C hC
  have hs := Finite.ClosedComponents.subset (Projective.MatrixFamily.Family.space A)
    (IsolatedGeometricComponents.intersection (Projective.MatrixFamily.Family.space A)
      (MovingFamily.Family.movingSupport X A W) (MovingFamily.Family.fixedSupport X A)) C hC
  have hout : Projective.MatrixFamily.Family.specialization A a ha (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)) ∉
      (C : Set (Projective.MatrixFamily.Family.space A)) := fun hy => hn (hs hy).1
  rw [GlobalParameterSum.Weights.weight, dite_eq_right hout, mul_zero]

theorem zero_coefficient (p : ℕ) (B : X.DimensionCycleSupport p)
    (hB : X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) ∉ (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) :
    MovingFamily.Family.cycle X A W p 0 B = 0 := by
  by_contra hn
  have hs := supported X A W p 0 (Polynomial.MatrixPath.zero_good A) B (Finsupp.mem_support_iff.mpr hn)
  have hm := hs (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem
  change X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) ∈
    Projective.MatrixFamily.Family.specialization A 0 (Polynomial.MatrixPath.zero_good A) ⁻¹'
      (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A)) at hm
  rw [zero_moving] at hm
  exact hB hm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingSupport
