import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopPushforward

/-! # Intrinsic Top Open Square -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopOpenSquare.Constructions

noncomputable section

/-! Native top pushforward commutes with actual restriction diagrams of open manifolds. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]

theorem nativeTopCohomologyPushforward_openSquare (U : Opens M) (V : Opens N)
    (fU : TopCat.of U ⟶ TopCat.of V) (f : TopCat.of M ⟶ TopCat.of N)
    (hs : fU ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) V = CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U ≫ f) :
    IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward (M := U) (N := V) (d := d) (e := e) fU ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of N) V (2*e) =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U (2*d) ≫
      IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward (M := M) (N := N) (d := d) (e := e) f := by
  have hL := IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward_comp (M := U) (N := V) (L := N)
    (d := d) (e := e) (k := e) fU (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) V)
  have hR := IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward_comp (M := U) (N := M) (L := N)
    (d := d) (e := d) (k := e) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U) f
  have hc := congrArg
    (IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward (M := U) (N := N) (d := d) (e := e)) hs
  rw [IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward_open] at hL hR
  exact hL.trans (hc.trans hR.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopOpenSquare.Constructions
