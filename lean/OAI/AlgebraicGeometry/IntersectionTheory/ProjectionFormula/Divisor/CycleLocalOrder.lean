import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalEquations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.EquationRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrincipalLeft
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder

/-! # Cycle Local Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleLocalOrder

noncomputable section

/-! Every proper divisor intersection multiplicity in every dimension is
the actual order of a local equation on the possibly singular other support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem exists_equation_order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (B : X.DimensionCycleSupport 1) (A : X.DimensionCycleSupport q)
    (C : X.DimensionCycleSupport (q + 1))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier)) (hAB : ¬ A.val ≤ B.val) :
    ∃ r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val), r ≠ 0 ∧
      RingHom.ker (Local.Principal.supportStalkMap X.carrier B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB).hom = Ideal.span {r} ∧
      Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA r ≠ 0 ∧
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val =
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).ord
          (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk
            (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA)) (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField
            (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA r))
          (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) : ℚ) := by
  obtain ⟨r, hr, he⟩ := Smooth.LocalEquations.exists_equation X m B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB
  have hra := Support.EquationRestriction.nonzero X.carrier A.val B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    hxA hxB r he hAB
  refine ⟨r, hr, he, hra, ?_⟩
  rw [Affine.PrincipalOrder.stalk_order _ _
    (AdjacentSupportStalk.coheight_one X m q A C hxA) _ hra, Int.cast_natCast]
  exact Local.PrincipalLeft.intersectionMultiplicity_eq_order X A.val B.val C.val hxA hxB r hr he hra

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleLocalOrder
