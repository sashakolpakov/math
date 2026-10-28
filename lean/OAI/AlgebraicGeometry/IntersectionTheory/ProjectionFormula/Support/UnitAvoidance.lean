import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalSupportUnits
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointMoving

/-! # Unit Avoidance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.UnitAvoidance

noncomputable section

/-! Finite point avoidance makes a rational function on a possibly
nonnormal support a unit along every component of its intersection with
the chosen divisor. The divisor is moved by actual rational equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem exceptional_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ) (W : X.DimensionCycleSupport k)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hf : f ≠ 0) :
    ∃ S : Finset X.carrier, ∀ D : X.DimensionCycleSupport 1,
      (∀ x ∈ S, x ∉ (D.val : Set X.carrier)) → (¬ W.val ≤ D.val) ∧
        ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
          CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
          ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
            algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
              (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = f := by
  obtain ⟨T, _, hu⟩ := RationalSupportUnits.exists_finite_exceptional (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) f hf
  let S := insert (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) (T.image fun y => CycleClass.Geometric.GenericPoint.reducedSupportι W.val y)
  refine ⟨S, fun D hD => ⟨?_, ?_⟩⟩
  · intro h
    exact hD (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) (Finset.mem_insert_self _ _)
      (h (W.val.isIrreducible.isGenericPoint_genericPoint W.val.isClosed).mem)
  · intro y hy hyD
    apply hu y hy
    intro hyT
    exact hD (CycleClass.Geometric.GenericPoint.reducedSupportι W.val y)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y, hyT, rfl⟩)) hyD

theorem move (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hf : f ≠ 0)
    (T : Finset X.carrier) (a : X.RationalDimensionCycle 1) :
    ∃ b : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a b ∧
      (∀ D ∈ b.support, ∀ x ∈ T, x ∉ (D.val : Set X.carrier)) ∧
      ∀ D ∈ b.support, (¬ W.val ≤ D.val) ∧
        ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
          CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
          ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
            algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
              (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = f := by
  obtain ⟨S, hS⟩ := exceptional_points X k W f hf
  obtain ⟨b, hb, hav⟩ := Divisor.PointMoving.move X m (S ∪ T) a
  refine ⟨b, hb, ?_, ?_⟩
  · intro D hD x hx
    exact hav D hD x (Finset.mem_union_right _ hx)
  · intro D hD
    exact hS D (fun x hx => hav D hD x (Finset.mem_union_left _ hx))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.UnitAvoidance
