import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Approximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Normal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports

/-! # Chow Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMoving

noncomputable section

/-! Divisor moving on every smooth projective presentation. Actual principal
divisors remove any finite list of divisor components, so two divisor cycles
always have rationally equivalent representatives meeting properly. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m

theorem exists_principal_separating (S : Finset (X.DimensionCycleSupport 1)) (A : S) :
    ∃ d : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X 1 d ∧
      ∀ B : S, d B.val = if B = A then 1 else 0 := by
  classical
  let C := ZeroComponents.containingComponent X m A.val.val
  let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι C.val) :=
    Open.Support.inclusion_isOpenImmersion C.val (Open.Support.codimension_zero_isOpen X m C)
  let : SmoothOfRelativeDimension m (CycleClass.Geometric.SupportFiniteType.supportStructureMap C.val X.structureMap) := by
    simpa only [zero_add, CycleClass.Geometric.SupportFiniteType.supportStructureMap] using
      (smoothOfRelativeDimension_comp 0 m (CycleClass.Geometric.GenericPoint.reducedSupportι C.val) X.structureMap)
  let : Smooth (CycleClass.Geometric.SupportFiniteType.supportStructureMap C.val X.structureMap) :=
    SmoothOfRelativeDimension.smooth m _
  let T := {B : S // CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val ∈ (C.val : Set X.carrier)}
  let y : T → CycleClass.Geometric.GenericPoint.reducedSupportScheme C.val := fun B =>
    CycleClass.Thom.IntersectionGeometry.supportPreimage C.val (CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val.val) B.property
  have hy (B : T) : CycleClass.Geometric.GenericPoint.reducedSupportι C.val (y B) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val.val :=
    CycleClass.Thom.IntersectionGeometry.supportPreimage_spec _ _ _
  have hheight (B : T) : Order.coheight (y B) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι C.val), hy]
    exact CurveSupports.coheight_one X m B.val.val
  have hinj : Function.Injective y := by
    intro B D h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply irreducibleSetEquivPoints.injective
    exact (hy B).symm.trans ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι C.val) h).trans (hy D))
  obtain ⟨g, hg, he⟩ := Projective.Approximation.exists_orders
    (X.projective.reducedSupport C.val)
    (ProjectionFormula.Smooth.Normal.stalk_integrallyClosed (CycleClass.Geometric.SupportFiniteType.supportStructureMap C.val X.structureMap))
    y hheight hinj (fun B => if B.val = A then 1 else 0)
  refine ⟨Principal.ClosedSectionCycle.principalCycle X 1 C.val g,
    Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor X 1 C.val (by rw [C.property]) g hg, fun B => ?_⟩
  rw [Principal.ClosedSectionCycle.principalCycle_apply]
  by_cases hB : CycleClass.Thom.IntersectionGeometry.supportPoint B.val.val ∈ (C.val : Set X.carrier)
  · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hB]
    have h := he (⟨B, hB⟩ : T)
    change (CycleClass.Geometric.GenericPoint.reducedSupportScheme C.val).ord g (CycleClass.Thom.IntersectionGeometry.supportPreimage C.val _ hB) =
      (if B = A then 1 else 0) at h
    rw [h]
    split_ifs <;> norm_num
  · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hB, ite_eq_right]
    intro h
    subst B
    exact hB ((ZeroComponents.subset_containingComponent X m A.val.val)
      (A.val.val.isIrreducible.isGenericPoint_genericPoint A.val.val.isClosed).mem)

theorem exists_rationallyEquivalent_avoiding (S : Finset (X.DimensionCycleSupport 1))
    (a : X.RationalDimensionCycle 1) :
    ∃ a' : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a' ∧
      ∀ B ∈ S, a' B = 0 := by
  classical
  choose d hd he using exists_principal_separating X m S
  let c := ∑ A : S, a A.val • d A
  refine ⟨a - c, ?_, fun B hB => ?_⟩
  · change a - (a - c) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
    rw [sub_sub_cancel]
    exact Submodule.sum_mem _ (fun A _ => Submodule.smul_mem _ _ (Submodule.subset_span (hd A)))
  · change a B - c B = 0
    simp only [c, Finsupp.finsetSum_apply, Finsupp.smul_apply]
    have h (A : S) : d A B = if (⟨B, hB⟩ : S) = A then 1 else 0 := he A ⟨B, hB⟩
    simp only [h, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

theorem meetProperly_of_avoiding (a b : X.RationalDimensionCycle 1)
    (h : ∀ B ∈ b.support, a B = 0) : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b := by
  intro A hA B hB C hC
  have hCA : C ≤ A.val := fun _ hx => (hC hx).1
  have hCB : C ≤ B.val := fun _ hx => (hC hx).2
  have hne : C ≠ A.val := by
    intro he
    have hAB : A = B := Subtype.ext
      (IntersectionZero.eq_of_subset_of_codimension_eq X m
        (he ▸ hCB) (A.property.trans B.property.symm))
    subst A
    exact (Finsupp.mem_support_iff.mp hA) (h B hB)
  have ht := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCA hne)
  rw [A.property] at ht
  omega

theorem properly_meeting_representatives (a b : X.RationalDimensionCycle 1) :
    ∃ a' : X.RationalDimensionCycle 1,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a' ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a' b := by
  obtain ⟨a', ha', havoid⟩ := exists_rationallyEquivalent_avoiding X m b.support a
  exact ⟨a', ha', meetProperly_of_avoiding X m a' b havoid⟩

theorem intersection_representative_exists (a b : X.RationalDimensionCycle 1) :
    ∃ c : X.RationalDimensionCycle (1 + 1), CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X 1 1 a b c := by
  obtain ⟨a', ha', hproper⟩ := properly_meeting_representatives X m a b
  obtain ⟨c, hc, _⟩ := Supports.ProperCycle.properIntersection_exists_unique X m 1 1 a' b hproper
  exact ⟨c, a', b, c, ha', CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 1 b, hc,
    CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (1 + 1) c⟩

theorem chowIntersection_nonempty (a b : ProperCycleLinearity.ChowQ X 1) :
    (ProperCycleLinearity.chowIntersection X 1 1 a b).Nonempty := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 b
  obtain ⟨c, hc⟩ := intersection_representative_exists X m a b
  exact ⟨ProperCycleLinearity.cycleToChowQ X (1 + 1) c, a, b, c, rfl, rfl, rfl, hc⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMoving
