import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothRelativeDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Geometric Abelian Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAbelianDimension

noncomputable section

/-! The fixed relative dimension of an actual abelian scheme agrees with
the Krull dimension of its geometric total space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension.Construction

theorem geometric_abelian_dimension {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) :
    topologicalKrullDim A.scheme.left = (g : WithBot ℕ∞) := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  have : JacobsonSpace A.scheme.left := LocallyOfFiniteType.jacobsonSpace A.scheme.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := A.scheme.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hdim : topologicalKrullDim A.scheme.left = ringKrullDim (A.scheme.left.presheaf.stalk x) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.scheme.left (fun y z hy hz => by
      obtain ⟨e, _, he, _⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations.Construction.multiplication_transitive_automorphisms A.scheme 1 y z hy hz
      exact ⟨e, he⟩) x hx
  exact hdim.trans (SmoothRelativeDimension.DimensionSupport.ringKrullDim_stalk_of_smoothOfRelativeDimension
    g A.scheme.hom x hx)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAbelianDimension
