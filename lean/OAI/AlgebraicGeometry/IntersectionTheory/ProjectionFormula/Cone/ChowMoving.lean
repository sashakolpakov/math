import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovingZeroCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CycleAmbientComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovingPosition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormMatrix

/-! # Chow Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.ChowMoving

noncomputable section

section

/-! The zero fiber of the actual moving family is precisely the
intrinsic cone intersection cycle, with its native Tor multiplicities. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace FamilyZero

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (p : ℕ) (W : X.DimensionCycleSupport p)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

theorem cycle :
    MovingFamily.Family.cycle X A (SupportBound.IntegralCycle.cone X m L hL h p W) p 0 =
      SupportBound.IntegralCycle.cycle X m L hL h p W := by
  ext B
  let K := SupportBound.IntegralCycle.cone X m L hL h p W
  by_cases hb : X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) ∈ (K : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))
  · let D := Closed.EmbeddingCycle.supportImage (EmbeddedFundamentalSupport.embedding X)
      m X.ambientDimension p (p + (X.ambientDimension - m)) (EmbeddedFundamentalSupport.degree X m p) B
    have hp : ∀ C : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension),
        (C : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ⊆ (K : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ∩
          Set.range X.embedding →
        p + (X.ambientDimension - m) ≤
          (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension C := by
      intro C hC
      have he := Proper.ambient_bound X m L hL h W.val C hC
      rwa [W.property] at he
    exact MovingZeroCoefficient.coefficient X A K p (p + (X.ambientDimension - m)) hp B D
      (Multiplicity.IntegralProjection.image_point X B.val) hb
  · rw [MovingSupport.zero_coefficient X A K p B hb]
    apply Eq.symm
    by_contra hn
    exact hb (SupportBound.IntegralCycle.coefficient_nonzero X m L hL h p W B hn)

end FamilyZero

end

/-! The actual cone intersection is rationally equivalent to a
cycle meeting every prescribed integral support properly. This combines
the native Tor zero-fiber identity with the geometric matrix translate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
    (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
    (p : ℕ) (W : X.DimensionCycleSupport p)
    {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier) :
    ∃ c : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (SupportBound.IntegralCycle.cycle X m L hL h p W) c ∧
      ∀ t, ∀ D ∈ c.support, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ (D.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
          p + X.supportCodimension (Z t) ≤ X.supportCodimension C := by
  let f : X.toOver ⟶ (Projective.Dimension.SpacePresentation.presentation m).toOver :=
    Over.homMk (Projection.FiniteProjective.FromForms.map X m L h) (Projection.FiniteProjective.FromForms.over_base X m L h)
  let : IsFinite f.left := inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h))
  let S := ProperCycleLinearity.imageSupport f W.val
  have hS : CycleClass.Thom.IntersectionGeometry.supportPoint S = Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) :=
    irreducibleSetEquivPoints.apply_symm_apply _
  have hSp : (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S = p :=
    (ProjectionFormula.Finite.Codimension.Projection.image f m W.val).trans W.property
  obtain ⟨e, _, hZ⟩ := MovingPosition.exists_translation X m L hL S Z
  rw [hS, hSp] at hZ
  let A := LinearFormMatrix.unit e
  let K := SupportBound.IntegralCycle.cone X m L hL h p W
  let c := MovingFamily.Family.cycle X A K p 1
  refine ⟨c, ?_, ?_⟩
  · have he := MovingFamily.Family.rationallyEquivalent X A K m p 0 1
      (Polynomial.MatrixPath.zero_good A) (Polynomial.MatrixPath.one_good A)
    rw [FamilyZero.cycle X m L hL h p W A] at he
    exact he
  · intro t D hD C hC
    have hs := MovingSupport.supported X A K p 1 (Polynomial.MatrixPath.one_good A) D hD
    apply hZ t C
    intro y hy
    refine ⟨?_, (hC hy).2⟩
    have hm := hs (hC hy).1
    change X.embedding y ∈ Projective.MatrixFamily.Family.specialization A 1 (Polynomial.MatrixPath.one_good A) ⁻¹'
      (MovingFamily.Family.movingSupport X A K : Set (Projective.MatrixFamily.Family.space A)) at hm
    rw [MovingSupport.one_moving, LinearFormMatrix.map] at hm
    exact hm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.ChowMoving
