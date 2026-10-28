import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ContainedFamilyInvariance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingSupport

/-! # Moving Family Invariance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingFamilyInvariance

noncomputable section

/-! The actual matrix-family moving cycle preserves proper intersection
with a fixed support whenever both full marked intersections are proper. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (W : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))
  (p q : ℕ) (B : X.DimensionCycleSupport q)

theorem proper_component (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hproper : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (MovingSupport.intersection X A W a ha : Set X.carrier) ∩
        (B.val : Set X.carrier) → p + q ≤ X.supportCodimension E)
    (C : IrreducibleCloseds (Projective.MatrixFamily.Family.space A)) (hCF : C ∈ MovingFamily.Family.components X A W)
    (hC : (C : Set (Projective.MatrixFamily.Family.space A)) ⊆ Set.range (Projective.FamilyOnSource.Family.toAmbient X A))
    (E : IrreducibleCloseds X.carrier)
    (hE : (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹'
      (ContainedHorizontalFamilyFiber.Family.support X A C hC : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier)) :
    p + q ≤ X.supportCodimension E := by
  have hsub := Finite.ClosedComponents.subset (Projective.MatrixFamily.Family.space A)
    (IsolatedGeometricComponents.intersection (Projective.MatrixFamily.Family.space A)
      (MovingFamily.Family.movingSupport X A W) (MovingFamily.Family.fixedSupport X A)) C hCF
  apply hproper E
  intro z hz
  refine ⟨?_, (hE hz).2⟩
  have hs : Projective.FamilyOnSource.Family.toAmbient X A (Projective.FamilyOnSource.Family.specialization X A a ha z) ∈ (C : Set (Projective.MatrixFamily.Family.space A)) :=
    (hE hz).1
  have hm := (hsub hs).1
  change (Projective.FamilyOnSource.Family.specialization X A a ha ≫ Projective.FamilyOnSource.Family.toAmbient X A) z ∈
    (MovingFamily.Family.movingSupport X A W : Set (Projective.MatrixFamily.Family.space A)) at hm
  rw [Projective.FamilyOnSource.Family.specialization_ambient] at hm
  exact hm

theorem equivalent (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0)
    (hproper_a : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (MovingSupport.intersection X A W a ha : Set X.carrier) ∩
        (B.val : Set X.carrier) → p + q ≤ X.supportCodimension E)
    (hproper_b : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (MovingSupport.intersection X A W b hb : Set X.carrier) ∩
        (B.val : Set X.carrier) → p + q ≤ X.supportCodimension E) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q)
      (Supports.ProperCycle.intersectionBilinear X m p q (MovingFamily.Family.cycle X A W p a) (Finsupp.single B 1))
      (Supports.ProperCycle.intersectionBilinear X m p q (MovingFamily.Family.cycle X A W p b) (Finsupp.single B 1)) :=
  ContainedFamilyInvariance.Family.equivalent X A m p q
    (MovingFamily.Family.coefficient X A W) (MovingFamily.Family.components X A W) B a b ha hb
    (proper_component X A W p q B a ha hproper_a) (proper_component X A W p q B b hb hproper_b)

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingFamilyInvariance
