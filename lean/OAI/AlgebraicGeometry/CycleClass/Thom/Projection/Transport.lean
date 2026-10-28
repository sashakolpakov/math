import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport

/-! # Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.Transport.Constructions.Class

noncomputable section

/-! Actual compact-fiber projection commutes with equality transports of
both support complements and both displayed degrees. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectComplement_transport (X : TopCat.{0}) (A A' : Set X) (hA : A = A')
    (K : Set M) (hK : IsCompact K) (D D' : Set (X × M)) (hD : D = D')
    (hb : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) A Kᶜ ⊆ D)
    (hb' : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) A' Kᶜ ⊆ D')
    (p p' n n' : ℕ) (hp : p = p') (hn : n = n')
    (hd : p + 2 * d = n) (hd' : p' + 2 * d = n')
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D n) :
    Supported.ProjectionCup.Constructions.projectComplement d X A' K hK D' hb' p' n' hd'
      (Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of (X × M)) hD hn c) =
    Supported.Transport.Constructions.Class.supportDegreeTransport X hA hp (Supported.ProjectionCup.Constructions.projectComplement d X A K hK D hb p n hd c) := by
  cases hA
  cases hD
  cases hp
  cases hn
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.Transport.Constructions.Class
