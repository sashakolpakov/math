import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality

/-! # Both Support Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.BothSupportEnlargement.Constructions

noncomputable section

/-! Supported projection commutes with simultaneous enlargement of the
actual source support and its actual base support. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectAt_support_enlargement (X : TopCat.{0}) (S S' : Set X) (hS : S ⊆ S')
    (K : Set M) (hK : IsCompact K) (T T' : Set (X × M))
    (hT : T ⊆ S ×ˢ K) (hT' : T' ⊆ S' ×ˢ K) (hTT : T ⊆ T')
    (p n : ℕ) (hn : p + 2 * d = n)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ n) :
    Supported.ProjectionDegree.Constructions.projectAt d X S' K hK T' hT' p n hn
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
        (A := T'ᶜ) (B := Tᶜ) (fun _ hx ht => hx (hTT ht)) n c) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (A := S'ᶜ) (B := Sᶜ) (fun _ hx hs => hx (hS hs)) p
      (Supported.ProjectionDegree.Constructions.projectAt d X S K hK T hT p n hn c) := by
  exact Supported.ProjectionDegreeNaturality.Constructions.projectAt_natural d (𝟙 X) S' S T' T K hK hT' hT
    (fun _ hx hs => hx (hS hs)) (fun _ hx ht => hx (hTT ht)) p n hn c

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.BothSupportEnlargement.Constructions
