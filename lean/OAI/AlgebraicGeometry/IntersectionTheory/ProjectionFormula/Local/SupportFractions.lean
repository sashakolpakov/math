import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeFractions

/-! # Support Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportFractions

noncomputable section

/-! The unit condition on the actual divisor intersection gives a
single fraction on every support stalk that is valid along all local
components of the divisor equation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_fraction (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (hDW : ¬ W.val ≤ D.val) (x : X.carrier)
    (hxD : x ∈ (D.val : Set X.carrier)) (hxW : x ∈ (W.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk x) (hr : r ≠ 0)
    (he : RingHom.ker (Principal.supportStalkMap X.carrier D.val x hxD).hom = Ideal.span {r})
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
      CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
        ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
          algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
            (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g) :
    let R := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
        Principal.supportStalkMap X.carrier W.val x hxW r ∈ p.asIdeal → a ∉ p.asIdeal ∧ b ∉ p.asIdeal) ∧
      g = algebraMap R (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField a /
        algebraMap R (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField b := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW
  let f := Principal.supportStalkMap X.carrier W.val x hxW r
  have hf : f ≠ 0 := SupportMultiplicity.restricted_nonzero X k D W hDW x hxD hxW r he
  apply Stalk.PrimeFractions.exists_fraction Y y f hf g hg
  intro p hp hfp
  let A : X.DimensionCycleSupport (1 + k) := ⟨Support.LocalDivisor.support X k W x hxW p,
    by rw [Support.LocalDivisor.codimension X k W x hxW p m hp]; omega⟩
  have hA : A ∈ (Divisor.SupportCycle.cycle X m k D W).support :=
    SupportMultiplicity.mem_cycle X m k D W hDW x hxD hxW r hr he p hp hfp
  have hAD := (Divisor.SupportCycle.support_subset X m k D W hDW A hA).1
  have hheight : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (Stalk.DivisorSupport.primeClosure Y y p)) = 1 := by
    rw [Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
    exact hp
  apply hunit _ hheight
  rw [Stalk.DivisorSupport.primeClosure_point, ← Support.LocalDivisor.support_point X k W x hxW p]
  exact hAD (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportFractions
