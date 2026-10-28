import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.PairPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology

/-! # Slice Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceRestriction.Constructions

noncomputable section

/-! Actual restriction of the closed-immersion Thom class to a normal slice and then a sheet neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.PairPullback.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions.LocalCoefficients OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E G W : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [ChartedSpace G N]
  [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] [ChartedSpace W L]
  [IsManifold 𝓘(ℂ, W) ω L]
  {c d : ℕ} {f : M → N} {x : M}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

local instance (priority := low) : ChartedSpace (G × (Fin d → ℂ)) (N × (Fin d → ℂ)) :=
  prodChartedSpace G N (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, G × (Fin d → ℂ)) ω (N × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

variable (i : L → N × (Fin d → ℂ))
  (hi : ContMDiff 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) ω i)
  (hii : ∀ y, Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y))
  (he : Topology.IsClosedEmbedding i)
  (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension W (G × (Fin d → ℂ)) = c + d)

def sliceThomClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ)))
    (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i))ᶜ (2 * (c + d)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SliceFiberEquiv.Constructions.Support.ambientSliceProduct P (TopCat.of (Fin d → ℂ)))
    (show Set.MapsTo (SliceFiberEquiv.Constructions.Support.ambientSliceProduct P (TopCat.of (Fin d → ℂ)))
      (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i))ᶜ (Set.range i)ᶜ from fun _ hx => hx)
    (2 * (c + d)) (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (c + d) hp)

theorem sliceThomClass_local (y : L)
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair W (Fin (c + d) → ℂ) i y)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G × (Fin d → ℂ))
      𝓘(ℂ, W × (Fin (c + d) → ℂ)))
    (V : Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ)))
    (hV : Set.MapsTo (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (id : (Fin d → ℂ) → (Fin d → ℂ)))
      (V : Set _) Q.neighborhood) (z : V)
    (hIso : ∀ a : V, Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id a.val ∈ Set.range i → a = z) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ))) (V : Set _))
      (Finite.PointCohomology.Constructions.LocalCoefficients.isolationMapsTo (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) V z hIso)
      (2 * (c + d)) (sliceThomClass P i hi hii he hp) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SliceNeighborhood.Constructions.sliceToPair P Q V hV)
      (SliceNeighborhood.Constructions.sliceToPair_mapsTo P Q V hV z hIso) (2 * (c + d)) Q.rationalClassFin := by
  let j := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ))) (V : Set _)
  let F := SliceFiberEquiv.Constructions.Support.ambientSliceProduct P (TopCat.of (Fin d → ℂ))
  let k := SliceNeighborhood.Constructions.sliceToPair P Q V hV
  let l := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (N × (Fin d → ℂ))) Q.neighborhood
  have hj := Finite.PointCohomology.Constructions.LocalCoefficients.isolationMapsTo (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) V z hIso
  have hF : Set.MapsTo F (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i))ᶜ (Set.range i)ᶜ :=
    fun _ hx => hx
  have hk := SliceNeighborhood.Constructions.sliceToPair_mapsTo P Q V hV z hIso
  have hs : j ≫ F = k ≫ l := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    rfl
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j F hj hF (2 * (c + d)))
    (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (c + d) hp)
  have h₂ := ConcreteCategory.congr_hom
    (Product.PointCanonical.Constructions.Class.relativeMap_congr hs (hF.comp hj)
      (show Set.MapsTo (k ≫ l) ({z}ᶜ) (Set.range i)ᶜ from hk) (2 * (c + d)))
    (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (c + d) hp)
  exact h₁.trans (h₂.trans (PairPullback.Constructions.ThomClass.normalPair_pullback i hi hii he (c + d) hp y Q hQ k ({z}ᶜ) hk))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceRestriction.Constructions
