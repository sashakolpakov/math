import OAI.ArithmeticGeometry.Descent.CMVariety.GroupFamilyDimension
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Dimension

noncomputable section

/-! The stated relative dimension of an actual geometric abelian
scheme is its topological dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}

theorem geometricAbelian_krullDim (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) :
    topologicalKrullDim A.scheme.left = (g : WithBot ℕ∞) := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  have : JacobsonSpace A.scheme.left := LocallyOfFiniteType.jacobsonSpace A.scheme.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := A.scheme.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  rw [PELModuli.IntegralModel.Group.LocalDimension.DimensionSupport.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.scheme.left
    (PELModuli.IntegralModel.Group.LocalDimension.DimensionSupport.closed_point_translations A.scheme) x hx]
  exact PELModuli.IntegralModel.SmoothRelativeDimension.DimensionSupport.ringKrullDim_stalk_of_smoothOfRelativeDimension g A.scheme.hom x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Dimension
