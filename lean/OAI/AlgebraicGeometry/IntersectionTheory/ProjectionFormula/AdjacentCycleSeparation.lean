import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingularOrderApproximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport

/-! # Adjacent Cycle Separation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentCycleSeparation

noncomputable section

/-! Actual principal divisors on possibly singular supports
separate finitely many supports in the next ambient codimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

theorem exists_principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport r)
    (S : Finset (X.DimensionCycleSupport (r + 1))) (C : X.DimensionCycleSupport (r + 1))
    (hC : C ∈ S) (hCA : C.val ≤ A.val) :
    ∃ (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField) (k : ℕ), g ≠ 0 ∧ 0 < k ∧
      ∀ B ∈ S, Principal.ClosedSectionCycle.principalCycle X (r + 1) A.val g B = if B = C then (k : ℚ) else 0 := by
  let T := {B : S // CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val ∈ (A.val : Set X.carrier)}
  let y : T → CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val := fun B => CycleClass.Thom.IntersectionGeometry.supportPreimage A.val
    (CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val.val) B.property
  have hy (B : T) : CycleClass.Geometric.GenericPoint.reducedSupportι A.val (y B) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val.val :=
    CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A.val _ B.property
  have hCx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier) :=
    hCA (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem
  let c : T := ⟨⟨C, hC⟩, hCx⟩
  let U := Finset.univ.image y
  have hU (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val) (hz : z ∈ U) : Order.coheight z = 1 := by
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hz
    exact AdjacentSupportStalk.coheight_one X m r A B.val.val B.property
  obtain ⟨g, k, hg, hk, he⟩ := SingularOrderApproximation.exists_separating
    (X.projective.reducedSupport A.val) U (y c) hU
  refine ⟨g, k, hg, hk, fun B hB => ?_⟩
  rw [Principal.ClosedSectionCycle.principalCycle_apply]
  by_cases hxB : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∈ (A.val : Set X.carrier)
  · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hxB]
    let b : T := ⟨⟨B, hB⟩, hxB⟩
    have hb := he (y b) (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
    have heq : y b = y c ↔ B = C := by
      constructor
      · intro h
        apply Subtype.ext
        apply irreducibleSetEquivPoints.injective
        exact (hy b).symm.trans ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι A.val) h).trans (hy c))
      · intro h
        subst B
        rfl
    change ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).ord g (y b) : ℚ) = _
    rw [hb, heq]
  · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hxB, ite_eq_right]
    intro h
    subst B
    exact hxB hCx

theorem exists_relation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport r)
    (S : Finset (X.DimensionCycleSupport (r + 1))) (C : X.DimensionCycleSupport (r + 1))
    (hC : C ∈ S) (hCA : C.val ≤ A.val) :
    ∃ d : X.RationalDimensionCycle (r + 1), d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (r + 1) ∧
      CycleSupport.SupportedOn X (r + 1) d ⟨A.val, A.val.isClosed⟩ ∧
      ∀ B ∈ S, d B = if B = C then 1 else 0 := by
  obtain ⟨g, k, hg, hk, he⟩ := exists_principal X m r A S C hC hCA
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  refine ⟨(k : ℚ)⁻¹ • Principal.ClosedSectionCycle.principalCycle X (r + 1) A.val g, ?_, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X (r + 1) A.val (by rw [A.property]) g hg))
  · intro B hB
    apply (Supports.supportPoint_mem_iff_subset
      (⟨A.val, A.val.isClosed⟩ : Closeds X.carrier) B.val).mp
    by_contra hn
    change CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∉ (A.val : Set X.carrier) at hn
    have hb := Finsupp.mem_support_iff.mp hB
    apply hb
    rw [Finsupp.smul_apply, Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hn, smul_zero]
  · intro B hB
    rw [Finsupp.smul_apply, he B hB, smul_eq_mul]
    split_ifs
    · exact inv_mul_cancel₀ hk0
    · exact mul_zero _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentCycleSeparation
