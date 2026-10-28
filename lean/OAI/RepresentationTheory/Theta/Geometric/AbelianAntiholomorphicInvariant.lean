import OAI.RepresentationTheory.Theta.Geometric.ClosedAntiholomorphicDeRham
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage

/-! # Abelian Antiholomorphic Invariant -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant

noncomputable section

/-! Actual closed antiholomorphic one-forms on an abelian variety are
translation invariant, by native averaging and uniqueness of pure representatives. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology

def abelianType01InvariantRepresentative (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace) :
    AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1 :=
  (AlgebraicGeometry.AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).symm
    (ClosedAntiholomorphicDeRham.closedType01DeRhamClass A.variety.analyticModel A.variety.analyticSpace a)

theorem abelianType01InvariantRepresentative_eq (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace) :
    (abelianType01InvariantRepresentative A a).val = a.val.val := by
  let : ConnectedSpace A.variety.analyticSpace := AlgebraicGeometry.AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : MeasurableSpace A.variety.analyticSpace := borel _
  let : BorelSpace A.variety.analyticSpace := ⟨rfl⟩
  let b := abelianType01InvariantRepresentative A a
  have hbclass : AlgebraicGeometry.AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 b =
      ClosedAntiholomorphicDeRham.closedType01DeRhamClass A.variety.analyticModel A.variety.analyticSpace a :=
    (AlgebraicGeometry.AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).apply_symm_apply _
  have hbtype : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree A.variety.analyticModel A.variety.analyticSpace 0 1 b.val.val := by
    apply (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantDeRham_mem_pure_iff (p := 0) (q := 1) b).mp
    rw [hbclass]
    rw [← ClosedAntiholomorphicDeRham.closedType01DeRhamClass_range]
    exact LinearMap.mem_range_self _ a
  have heq : (⟨AlgebraicGeometry.AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1 b, hbtype⟩ :
      AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms A.variety.analyticModel A.variety.analyticSpace 0 1) =
      ClosedAntiholomorphicDeRham.closedType01PureClosedEquiv A.variety.analyticModel A.variety.analyticSpace a :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.antiholomorphic_formClass_injective hbclass
  exact congrArg (fun z : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms
    A.variety.analyticModel A.variety.analyticSpace 0 1 => z.val.val) heq

theorem abelian_closedType01_invariant (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace) :
    a.val.val ∈ AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1 := by
  rw [← abelianType01InvariantRepresentative_eq A a]
  exact (abelianType01InvariantRepresentative A a).property

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant
