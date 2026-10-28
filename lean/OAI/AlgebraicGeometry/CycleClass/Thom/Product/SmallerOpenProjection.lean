import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality

/-! # Smaller Open Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenProjection.Constructions

noncomputable section

/-! Actual bounded graph Thom projection commutes with the actual inclusion of a smaller ambient open. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L N E G : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E L]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (U P : Opens N) (hP : P ≤ U) {d : ℕ}

local instance (priority := low) (V : Opens N) : ChartedSpace (G × (Fin d → ℂ)) (V × (Fin d → ℂ)) :=
  prodChartedSpace G V (Fin d → ℂ) (Fin d → ℂ)

variable (i : L → U × (Fin d → ℂ)) (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G × (Fin d → ℂ)) ω i)
  (S : Set U) (K : Set (Fin d → ℂ))

theorem smallerGraph_bound (hT : Set.range i ⊆ S ×ˢ K) :
    Set.range (SmallerOpen.Constructions.smallerGraph U P hP i hi) ⊆ ((Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) ⁻¹' S) ×ˢ K := by
  rintro _ ⟨x, rfl⟩
  exact hT ⟨x.val, rfl⟩

variable [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℂ, E) ω L]
  [FiniteDimensional ℂ G] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]

local instance (V : Opens N) : MetrizableSpace V := V.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (V : Opens N) : IsManifold 𝓘(ℂ, G × (Fin d → ℂ)) ω (V × (Fin d → ℂ)) :=
  Immersion.Constructions.productModel_isManifold

theorem project_Thom_smaller
    (hii : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G × (Fin d → ℂ)) i x))
    (hc : Topology.IsClosedEmbedding i) (c : ℕ)
    (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E (G × (Fin d → ℂ)) = c + d)
    (hK : IsCompact K) (hT : Set.range i ⊆ S ×ˢ K) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of P) ((Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) ⁻¹' S) K hK
      (Set.range (SmallerOpen.Constructions.smallerGraph U P hP i hi)) (smallerGraph_bound U P hP i hi S K hT)
      (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree (SmallerOpen.Constructions.smallerGraph U P hP i hi) (SmallerOpen.Constructions.smallerGraph_analytic U P hP i hi)
        (SmallerOpen.Constructions.smallerGraph_differential_injective U P hP i hi hii) (SmallerOpen.Constructions.smallerGraph_closedEmbedding U P hP i hi hc) (c + d) hp) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) (fun _ hx => hx) (2 * c)
        (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) S K hK (Set.range i) hT (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm
          (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (c + d) hp)) := by
  have h := Supported.ProjectionDegreeNaturality.Constructions.projectAt_natural d (Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) ((Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) ⁻¹' S) S
    (Set.range (SmallerOpen.Constructions.smallerGraph U P hP i hi)) (Set.range i) K hK (smallerGraph_bound U P hP i hi S K hT) hT
    (fun _ hx => hx) (SmallerOpen.Constructions.smallerGraph_mapsTo U P hP i hi) (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm
    (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc (c + d) hp)
  exact (congrArg (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of P) ((Open.SubsetHomeomorph.Constructions.smallerOpenMap U P hP) ⁻¹' S) K hK
    (Set.range (SmallerOpen.Constructions.smallerGraph U P hP i hi)) (smallerGraph_bound U P hP i hi S K hT)
    (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm)
    (SmallerOpen.Constructions.smallerGraph_Thom_pullback U P hP i hi hii hc (c + d) hp).symm).trans h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenProjection.Constructions
