import OAI.RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Closed Antiholomorphic De Rham -/

namespace OAI.RepresentationTheory.Theta.Geometric.ClosedAntiholomorphicDeRham

noncomputable section

/-! The closed forms used in the Dolbeault model are the native pure
closed manifold forms, and their actual de Rham class map is injective. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def closedType01PureClosedEquiv : ClosedPureDolbeaultMap.ClosedType01Forms E M ≃ₗ[ℂ]
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms E M 0 1 where
  toFun a := ⟨⟨a.val.val, a.property⟩, a.val.property⟩
  invFun a := ⟨⟨a.val.val, a.property⟩, a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem closedType01PureClosedEquiv_coe (a : ClosedPureDolbeaultMap.ClosedType01Forms E M) :
    (closedType01PureClosedEquiv E M a).val.val = a.val.val := rfl

def closedType01DeRhamClass :
    ClosedPureDolbeaultMap.ClosedType01Forms E M →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M 1 :=
  (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass E M 0 1).comp
    (closedType01PureClosedEquiv E M).toLinearMap

theorem closedType01DeRhamClass_injective [FiniteDimensional ℝ E] [CompactSpace M] :
    Function.Injective (closedType01DeRhamClass E M) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.antiholomorphic_formClass_injective (E := E) (M := M)).comp
    (closedType01PureClosedEquiv E M).injective

theorem closedType01DeRhamClass_range :
    LinearMap.range (closedType01DeRhamClass E M) = AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage E M 0 1 := by
  rw [closedType01DeRhamClass, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (closedType01PureClosedEquiv E M).surjective)]
  exact AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.range_manifoldPureFormClass E M 0 1

def closedType01DeRhamEquiv [FiniteDimensional ℝ E] [CompactSpace M] :
    ClosedPureDolbeaultMap.ClosedType01Forms E M ≃ₗ[ℂ] AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage E M 0 1 :=
  (LinearEquiv.ofInjective (closedType01DeRhamClass E M)
    (closedType01DeRhamClass_injective E M)).trans
      (LinearEquiv.ofEq _ _ (closedType01DeRhamClass_range E M))

theorem closedType01DeRhamEquiv_coe [FiniteDimensional ℝ E] [CompactSpace M]
    (a : ClosedPureDolbeaultMap.ClosedType01Forms E M) :
    (closedType01DeRhamEquiv E M a).val = closedType01DeRhamClass E M a := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.ClosedAntiholomorphicDeRham
