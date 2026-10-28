import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Dimension Drop -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DimensionDrop

noncomputable section

/-! Principal divisors whose ambient support loses at least two dimensions
have zero proper pushforward. This discharges that geometric case of
rational-equivalence descent directly on the constructed cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

theorem imageSupport_mono {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) {A W : IrreducibleCloseds X.carrier} (h : A ≤ W) :
    ProperCycleLinearity.imageSupport f A ≤ ProperCycleLinearity.imageSupport f W := by
  change (ProperCycleLinearity.imageSupport f A : Set Y.carrier) ⊆ ProperCycleLinearity.imageSupport f W
  rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image]
  exact Set.image_mono h

theorem support_le_of_coefficient_ne_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W C : IrreducibleCloseds X.carrier) (a : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (h : CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W a C ≠ 0) : C ≤ W := by
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (W : Set X.carrier) := by
    by_contra hn
    exact h (dite_eq_right hn)
  have hC : closure {CycleClass.Thom.IntersectionGeometry.supportPoint C} = (C : Set X.carrier) :=
    congrArg (fun A : IrreducibleCloseds X.carrier => (A : Set X.carrier))
      (irreducibleSetEquivPoints.symm_apply_apply C)
  change (C : Set X.carrier) ⊆ W
  rw [← hC]
  exact W.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)

theorem cyclePushforward_eq_zero_of_image_dimension_lt
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (n p q : ℕ) [SmoothOfRelativeDimension n Y.structureMap]
    (W : IrreducibleCloseds X.carrier) (c : X.RationalDimensionCycle p)
    (hc : ∀ A ∈ c.support, A.val ≤ W)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap + q < n) :
    ProperCycleLinearity.cyclePushforward f p q c = 0 := by
  rw [ProperCycleLinearity.cyclePushforward, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro A hA
  have hle := (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono Y.structureMap).monotone
    (imageSupport_mono f (hc A hA))
  have hn : Y.supportCodimension (ProperCycleLinearity.imageSupport f A.val) ≠ q := by
    intro hq
    have h := Grading.supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f A.val)
    rw [hq] at h
    omega
  simp only [ProperCycleLinearity.cyclePushforwardGenerator, CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_right hn,
    smul_zero]

/-- A dimension drop of at least two kills the pushforward of every
principal divisor on that support. No norm or moving hypothesis is needed. -/
theorem principalCycle_pushforward_eq_zero_of_dimension_drop
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (m n p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (hdeg : p + n = q + m)
    (W : IrreducibleCloseds X.carrier) (hW : X.supportCodimension W + 1 = p)
    (a : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (hdrop : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap + 1 <
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap) :
    ProperCycleLinearity.cyclePushforward f p q (Principal.ClosedSectionCycle.principalCycle X p W a) = 0 := by
  apply cyclePushforward_eq_zero_of_image_dimension_lt f n p q W
  · intro C hC
    apply support_le_of_coefficient_ne_zero X W C.val a
    rw [← Principal.ClosedSectionCycle.principalCycle_apply X p W a C]
    exact Finsupp.mem_support_iff.mp hC
  · have h := Grading.supportDimension_add_codimension X m W
    omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DimensionDrop
