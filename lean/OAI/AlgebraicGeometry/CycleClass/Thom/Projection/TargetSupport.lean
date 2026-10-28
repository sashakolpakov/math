import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree

/-! # Target Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport.Constructions

noncomputable section

/-! Equality of actual base supports transports the actual supported projection with no change of class. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectAt_targetCast (X : TopCat.{0}) (S S' : Set X) (hS : S = S') (K : Set M) (hK : IsCompact K)
    (T : Set (X × M)) (hT : T ⊆ S ×ˢ K) (hT' : T ⊆ S' ×ˢ K) (p n : ℕ) (hn : p + 2 * d = n)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ n) :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Aᶜ p) hS)
      (Supported.ProjectionDegree.Constructions.projectAt d X S K hK T hT p n hn c) = Supported.ProjectionDegree.Constructions.projectAt d X S' K hK T hT' p n hn c := by
  subst S'
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport.Constructions
