import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionNaturality

/-! # Projection Degree Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality.Constructions

noncomputable section

/-! Actual supported projection commutes with base maps in any equal presentation of the input degree. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionNaturality.Constructions

theorem projectAt_natural (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set X) (S' : Set Y)
    (T : Set (X × M)) (T' : Set (Y × M)) (K : Set M) (hK : IsCompact K)
    (hT : T ⊆ S ×ˢ K) (hT' : T' ⊆ S' ×ˢ K) (hf : Set.MapsTo f Sᶜ S'ᶜ)
    (hF : Set.MapsTo
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 (TopCat.of M)) : (X, TopCat.of M) ⟶ (Y, TopCat.of M))) Tᶜ T'ᶜ)
    (p n : ℕ) (hn : p + 2 * d = n)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Y × M)) T'ᶜ n) :
    ProjectionDegree.Constructions.projectAt d X S K hK T hT p n hn
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, 𝟙 (TopCat.of M)) : (X, TopCat.of M) ⟶ (Y, TopCat.of M))) hF n c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p
        (ProjectionDegree.Constructions.projectAt d Y S' K hK T' hT' p n hn c) := by
  subst n
  exact ProjectionNaturality.Constructions.projectSupported_natural d f S S' T T' K hK hT hT' hf hF p c

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality.Constructions
