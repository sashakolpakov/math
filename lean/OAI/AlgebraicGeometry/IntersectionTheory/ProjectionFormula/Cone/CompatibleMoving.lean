import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.ChowMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingFamilyInvariance
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleRelations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportCycles

/-! # Compatible Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CompatibleMoving

noncomputable section

/-! A full cone intersection can be moved into any finite set of
positions while preserving its intersections with every fixed support
that the full original cone meets properly. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
    (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
    (p q : ℕ) (W : X.DimensionCycleSupport p)
    {τ ι : Type} [Finite τ] [Finite ι] (Z : τ → IrreducibleCloseds X.carrier) (B : ι → X.DimensionCycleSupport q)
    (hproper : ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (SupportBound.IntegralCycle.intersection X m L hL h p W : Set X.carrier) ∩
        ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      SupportBound.IntegralCycle.cycle X m L hL h p W - c ∈ CompatibleRelations.submodule X m p q B ∧
      c ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) := by
  let f : X.toOver ⟶ (Projective.Dimension.SpacePresentation.presentation m).toOver :=
    Over.homMk (Projection.FiniteProjective.FromForms.map X m L h) (Projection.FiniteProjective.FromForms.over_base X m L h)
  let : IsFinite f.left := inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h))
  let S := ProperCycleLinearity.imageSupport f W.val
  have hS : CycleClass.Thom.IntersectionGeometry.supportPoint S = Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) :=
    irreducibleSetEquivPoints.apply_symm_apply _
  have hSp : (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S = p :=
    (ProjectionFormula.Finite.Codimension.Projection.image f m W.val).trans W.property
  let T := Sum.elim Z (fun i => (B i).val)
  obtain ⟨e, _, hZ⟩ := MovingPosition.exists_translation X m L hL S T
  rw [hS, hSp] at hZ
  let A := LinearFormMatrix.unit e
  let K := SupportBound.IntegralCycle.cone X m L hL h p W
  let c := MovingFamily.Family.cycle X A K p 1
  have hfinal (t : τ ⊕ ι) (C : IrreducibleCloseds X.carrier)
      (hC : (C : Set X.carrier) ⊆
        (MovingSupport.intersection X A K 1 (Polynomial.MatrixPath.one_good A) : Set X.carrier) ∩
          (T t : Set X.carrier)) : p + X.supportCodimension (T t) ≤ X.supportCodimension C := by
    apply hZ t C
    intro y hy
    refine ⟨?_, (hC hy).2⟩
    have hm := (hC hy).1
    change X.embedding y ∈ Projective.MatrixFamily.Family.specialization A 1 (Polynomial.MatrixPath.one_good A) ⁻¹'
      (MovingFamily.Family.movingSupport X A K : Set (Projective.MatrixFamily.Family.space A)) at hm
    rw [MovingSupport.one_moving, LinearFormMatrix.map] at hm
    exact hm
  refine ⟨c, ?_, ?_⟩
  · apply (CompatibleRelations.mem_iff X m p q B _ c).mpr
    refine ⟨?_, ?_⟩
    · have he := MovingFamily.Family.rationallyEquivalent X A K m p 0 1
        (Polynomial.MatrixPath.zero_good A) (Polynomial.MatrixPath.one_good A)
      rw [ChowMoving.FamilyZero.cycle X m L hL h p W A] at he
      exact he
    · intro i
      have hzero (C : IrreducibleCloseds X.carrier)
          (hC : (C : Set X.carrier) ⊆
            (MovingSupport.intersection X A K 0 (Polynomial.MatrixPath.zero_good A) : Set X.carrier) ∩
              ((B i).val : Set X.carrier)) : p + q ≤ X.supportCodimension C := by
        apply hproper i C
        intro y hy
        refine ⟨?_, (hC hy).2⟩
        have hm := (hC hy).1
        change X.embedding y ∈ Projective.MatrixFamily.Family.specialization A 0 (Polynomial.MatrixPath.zero_good A) ⁻¹'
          (MovingFamily.Family.movingSupport X A K : Set (Projective.MatrixFamily.Family.space A)) at hm
        rw [MovingSupport.zero_moving] at hm
        exact hm
      have hone (C : IrreducibleCloseds X.carrier)
          (hC : (C : Set X.carrier) ⊆
            (MovingSupport.intersection X A K 1 (Polynomial.MatrixPath.one_good A) : Set X.carrier) ∩
              ((B i).val : Set X.carrier)) : p + q ≤ X.supportCodimension C := by
        have hbound := hfinal (Sum.inr i) C hC
        change p + X.supportCodimension (B i).val ≤ X.supportCodimension C at hbound
        rw [(B i).property] at hbound
        exact hbound
      have he := MovingFamilyInvariance.Family.equivalent X A K p q (B i) m 0 1
        (Polynomial.MatrixPath.zero_good A) (Polynomial.MatrixPath.one_good A) hzero hone
      rw [ChowMoving.FamilyZero.cycle X m L hL h p W A] at he
      exact he
  · intro t D hD C hC
    have hs := MovingSupport.supported X A K p 1 (Polynomial.MatrixPath.one_good A) D hD
    exact hfinal t C (fun y hy => ⟨hs (hC hy).1, (hC hy).2⟩)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CompatibleMoving
