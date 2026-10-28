import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import Mathlib.Algebra.DirectSum.Module

/-! # Decomposition -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM

noncomputable section

/-!
# CM decompositions with possibly different coefficient fields

Each component is an actual rational subspace of a weight-one Hodge
structure. Its inclusion preserves Hodge type, and it carries a rank-one
action of a CM number field. The fields are allowed to vary by component.
The internal-direct-sum condition asserts that these subspaces give the
whole rational vector space, with uniqueness of the decomposition.
-/

open scoped DirectSum

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

/-- One rank-one CM summand of a rational weight-one Hodge structure. -/
structure CMComponent (H : WeightOne.CM.WeightOneHodgeStructure U) where
  subspace : Submodule ℚ U
  hodge : WeightOne.CM.WeightOneHodgeStructure subspace
  inclusion_hodge : WeightOne.CM.IsHodgeMap hodge H subspace.subtype
  field : Type
  [fieldStructure : Field field]
  [fieldAlgebra : Algebra ℚ field]
  [scalarAction : Module field subspace]
  [scalarTower : IsScalarTower ℚ field subspace]
  cm : WeightOne.CM.RankOneCMAction field hodge

attribute [instance] CMComponent.fieldStructure CMComponent.fieldAlgebra
  CMComponent.scalarAction CMComponent.scalarTower

/-- The exact finite-direct-sum hypothesis of the manuscript, at the level
of rational Hodge structures. This contains no cycle-class hypothesis. -/
structure CMDecomposition (H : WeightOne.CM.WeightOneHodgeStructure U) where
  numberOfComponents : ℕ
  component : Fin numberOfComponents → CMComponent H
  isInternal : DirectSum.IsInternal (fun i => (component i).subspace)

namespace CMDecomposition

variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : CMDecomposition H)

/-- The sum map itself is an isomorphism, so the stated decomposition is
neither just a spanning family nor an assumed cohomological conclusion. -/
def linearEquiv : (⨁ i, (D.component i).subspace) ≃ₗ[ℚ] U :=
  LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun i => (D.component i).subspace)) D.isInternal

/-- On each summand the direct-sum isomorphism is its actual subtype inclusion. -/
@[simp]
theorem linearEquiv_lof (i : Fin D.numberOfComponents) (x : (D.component i).subspace) :
    D.linearEquiv
      (DirectSum.lof ℚ (Fin D.numberOfComponents) (fun j => (D.component j).subspace) i x) =
      (x : U) := by
  exact DirectSum.coeLinearMap_lof (fun j => (D.component j).subspace) i x

/-- Each rational summand has the degree of its own CM field. -/
theorem component_finrank (i : Fin D.numberOfComponents) :
    Module.finrank ℚ (D.component i).subspace = Module.finrank ℚ (D.component i).field :=
  (D.component i).cm.rational_finrank

end CMDecomposition

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM
