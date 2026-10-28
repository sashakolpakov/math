import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.FundamentalClass.AffineOrientation
import OAI.AlgebraicTopology.FundamentalClass.SimplexCycles

/-! # Affine Cycle -/

namespace OAI.AlgebraicTopology.FundamentalClass.AffineCycle.IntegrationConstruction

noncomputable section

section

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open _root_.CategoryTheory Opposite Set
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def affineSingularSimplex (d : ℕ) (a : Fin d → ℝ) (r : ℝ) :
    Cohomology.Singular.Basic.singularSimplices (TopCat.of (Fin d → ℝ)) d :=
  (TopCat.toSSet.map (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r)).app _ (LocalSimplex.IntegrationGeometry.positiveSingularSimplex d)

theorem affineSimplex_faces_avoid (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (K : Set (Fin d → ℝ)) (hK : K ⊆ AffineOrientation.IntegrationConstruction.affineInterior d a r) :
    SimplexCycles.IntegrationConstruction.SimplexFacesIn (TopCat.of (Fin d → ℝ)) Kᶜ d (affineSingularSimplex d a r) := by
  cases d with
  | zero => trivial
  | succ d =>
    intro i t ht
    have hmem := hK ht
    obtain ⟨y, hy, heq⟩ := hmem
    change AffineOrientation.IntegrationConstruction.positiveAffine (Fin (d + 1) → ℝ) a r y =
      AffineOrientation.IntegrationConstruction.positiveAffine (Fin (d + 1) → ℝ) a r
        (LocalSimplex.IntegrationGeometry.positiveSimplex (d + 1) (Convexity.StdSimplex.map i.succAbove t)) at heq
    have hy' := AffineOrientation.IntegrationConstruction.positiveAffine_injective (Fin (d + 1) → ℝ) a r hr heq
    exact SimplexGeometry.IntegrationConstruction.positiveSimplex_face_outside d i t (hy' ▸ hy)

theorem affineInteriorClass_eq_projectedClass (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) :
    AffineOrientation.IntegrationConstruction.affineInteriorClass d a r hr =
      ProjectedClasses.IntegrationConstruction.projectedClass (TopCat.of (Fin d → ℝ)) (AffineOrientation.IntegrationConstruction.affineInterior d a r)ᶜ d
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ)))
          (affineSingularSimplex d a r))
        (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle _ _ d _
          (affineSimplex_faces_avoid d a r hr _ (Subset.refl _))) := by
  rw [AffineOrientation.IntegrationConstruction.affineInteriorClass, SimplexSupport.IntegrationConstruction.positiveInteriorClass]
  change HomologicalComplex.homologyMap
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r)
      (AffineOrientation.IntegrationConstruction.positiveAffine_mapsTo_complement d a r hr)) d (Cohomology.Singular.ChainRepresentatives.chainClass _ d _) = _
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass _ d)
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r)
      (AffineOrientation.IntegrationConstruction.positiveAffine_mapsTo_complement d a r hr)) d)
    (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))) (LocalSimplex.IntegrationGeometry.positiveSingularSimplex d))
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r)
      (AffineOrientation.IntegrationConstruction.positiveAffine_mapsTo_complement d a r hr)).f d
      (SimplexSupport.IntegrationConstruction.positiveInteriorChain d) =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of (Fin d → ℝ)) (AffineOrientation.IntegrationConstruction.affineInterior d a r)ᶜ).f d
      ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) (TopCat.toSSet.map (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r))).f d
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))) (LocalSimplex.IntegrationGeometry.positiveSingularSimplex d))) at h
  rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex] at h
  exact h

theorem projectedClass_restrict (X : TopCat.{0}) {K L : Set X} (hKL : K ⊆ L) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (hL : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Lᶜ).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Lᶜ) n)
    (hK : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n c ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X Kᶜ) n) :
    AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction X hKL n (ProjectedClasses.IntegrationConstruction.projectedClass X Lᶜ n c hL) =
      ProjectedClasses.IntegrationConstruction.projectedClass X Kᶜ n c hK := by
  change HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL) n
    (Cohomology.Singular.ChainRepresentatives.chainClass _ n _) = _
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  apply congrArg (Cohomology.Singular.ChainRepresentatives.chainClass _ n)
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_projection X hKL) n) c

theorem affineProjectedClass_eq_coordinateCompactClass (d : ℕ) (a : Fin d → ℝ)
    (r : ℝ) (hr : 0 < r) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (hKs : K ⊆ AffineOrientation.IntegrationConstruction.affineInterior d a r) :
    ProjectedClasses.IntegrationConstruction.projectedClass (TopCat.of (Fin d → ℝ)) Kᶜ d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))) (affineSingularSimplex d a r))
      (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle _ _ d _ (affineSimplex_faces_avoid d a r hr K hKs)) =
      IntegrationOrientation.Geometry.coordinateCompactClass d K hK := by
  rw [← AffineOrientation.IntegrationConstruction.affineInteriorClass_restrict_compact d a r hr K hK hKs,
    affineInteriorClass_eq_projectedClass, projectedClass_restrict]

end

/-! An actual affine chart simplex represents the geometric compact chart
class. Chart excision is applied to its codomain-restricted simplex. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open _root_.CategoryTheory Opposite Set
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def chartLiftSimplex {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) (n : ℕ)
    (σ : Cohomology.Singular.Basic.singularSimplices X n) (hs : ∀ t, X.toSSetObjEquiv (op ⦋n⦌) σ t ∈ e.source) :
    Cohomology.Singular.Basic.singularSimplices (TopCat.of e.source) n :=
  ((TopCat.of e.source).toSSetObjEquiv (op ⦋n⦌)).symm
    ⟨fun t => ⟨X.toSSetObjEquiv (op ⦋n⦌) σ t, hs t⟩,
      (X.toSSetObjEquiv (op ⦋n⦌) σ).continuous.subtype_mk _⟩

theorem chartLiftSimplex_inclusion {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) (n : ℕ)
    (σ : Cohomology.Singular.Basic.singularSimplices X n) (hs : ∀ t, X.toSSetObjEquiv (op ⦋n⦌) σ t ∈ e.source) :
    (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source)).app _ (chartLiftSimplex e n σ hs) = σ := by
  apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
  rfl

theorem chartLiftSimplex_faces {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) (K : Set X)
    (n : ℕ) (σ : Cohomology.Singular.Basic.singularSimplices X n)
    (hs : ∀ t, X.toSSetObjEquiv (op ⦋n⦌) σ t ∈ e.source)
    (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn X Kᶜ n σ) :
    SimplexCycles.IntegrationConstruction.SimplexFacesIn (TopCat.of e.source) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ n
      (chartLiftSimplex e n σ hs) := by
  cases n with
  | zero => trivial
  | succ n => exact fun i t => hσ i t

def chartModelSimplex {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) (n : ℕ)
    (σ : Cohomology.Singular.Basic.singularSimplices X n) (hs : ∀ t, X.toSSetObjEquiv (op ⦋n⦌) σ t ∈ e.source) :
    Cohomology.Singular.Basic.singularSimplices Y n :=
  (TopCat.toSSet.map (ProjectedClasses.IntegrationConstruction.chartSourceToModel e)).app _ (chartLiftSimplex e n σ hs)

theorem chartModelSimplex_faces {X Y : TopCat.{0}} (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hKs : K ⊆ e.source) (n : ℕ) (σ : Cohomology.Singular.Basic.singularSimplices X n)
    (hs : ∀ t, X.toSSetObjEquiv (op ⦋n⦌) σ t ∈ e.source)
    (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn X Kᶜ n σ) :
    SimplexCycles.IntegrationConstruction.SimplexFacesIn Y (e '' K)ᶜ n (chartModelSimplex e n σ hs) := by
  cases n with
  | zero => trivial
  | succ n =>
    intro i t ht
    obtain ⟨z, hz, heq⟩ := ht
    have heq' : z = X.toSSetObjEquiv _ σ (Convexity.StdSimplex.map i.succAbove t) :=
      e.injOn (hKs hz) (hs _) heq
    exact hσ i t (heq' ▸ hz)

theorem chartProjectedSimplex_transport {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (n : ℕ) (σ : Cohomology.Singular.Basic.singularSimplices X n)
    (hs : ∀ t, X.toSSetObjEquiv (op ⦋n⦌) σ t ∈ e.source) (hσ : SimplexCycles.IntegrationConstruction.SimplexFacesIn X Kᶜ n σ) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso e K hK hKs n).hom
      (ProjectedClasses.IntegrationConstruction.projectedClass X Kᶜ n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)
        (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle X Kᶜ n σ hσ)) =
      ProjectedClasses.IntegrationConstruction.projectedClass Y (e '' K)ᶜ n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj Y) (chartModelSimplex e n σ hs))
        (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle Y (e '' K)ᶜ n _ (chartModelSimplex_faces e K hKs n σ hs hσ)) := by
  let c := Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of e.source)) (chartLiftSimplex e n σ hs)
  have hinc : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source)).f n c =
      Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ := by
    change (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source))).f n _ = _
    rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, chartLiftSimplex_inclusion]
  have hmodel : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (ProjectedClasses.IntegrationConstruction.chartSourceToModel e)).f n c =
      Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj Y) (chartModelSimplex e n σ hs) :=
    Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex _ _
  have hsource := SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle (TopCat.of e.source)
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source) ⁻¹' K)ᶜ n _ (chartLiftSimplex_faces e K n σ hs hσ)
  have hambient := SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle X Kᶜ n σ hσ
  have htarget := SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle Y (e '' K)ᶜ n _ (chartModelSimplex_faces e K hKs n σ hs hσ)
  rw [← hinc] at hambient
  rw [← hmodel] at htarget
  have h := ProjectedClasses.IntegrationConstruction.compactSupportChartHomologyIso_projectedClass e K hK hKs n c hsource hambient htarget
  simpa only [hinc, hmodel] using h

theorem chartSimplex_faces_avoid {X : TopCat.{0}} {d : ℕ}
    (e : OpenPartialHomeomorph X (Fin d → ℝ)) (K : Set X) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (hK : e '' K ⊆ AffineOrientation.IntegrationConstruction.affineInterior d a r) (σ : Cohomology.Singular.Basic.singularSimplices X d)
    (hcoords : ∀ t, e (X.toSSetObjEquiv (op ⦋d⦌) σ t) =
      AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (LocalSimplex.IntegrationGeometry.positiveSimplex d t)) :
    SimplexCycles.IntegrationConstruction.SimplexFacesIn X Kᶜ d σ := by
  cases d with
  | zero => trivial
  | succ d =>
    intro i t ht
    have hk := hK ⟨X.toSSetObjEquiv _ σ (Convexity.StdSimplex.map i.succAbove t), ht, rfl⟩
    rw [hcoords] at hk
    obtain ⟨y, hy, heq⟩ := hk
    exact SimplexGeometry.IntegrationConstruction.positiveSimplex_face_outside d i t
      ((AffineOrientation.IntegrationConstruction.positiveAffine_injective (Fin (d + 1) → ℝ) a r hr heq) ▸ hy)

theorem chartProjectedSimplex_eq_chartCompactClass {X : TopCat.{0}} [T2Space X] {d : ℕ}
    (e : OpenPartialHomeomorph X (Fin d → ℝ)) (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) (hKi : e '' K ⊆ AffineOrientation.IntegrationConstruction.affineInterior d a r)
    (σ : Cohomology.Singular.Basic.singularSimplices X d) (hs : ∀ t, X.toSSetObjEquiv (op ⦋d⦌) σ t ∈ e.source)
    (hcoords : ∀ t, e (X.toSSetObjEquiv (op ⦋d⦌) σ t) =
      AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (LocalSimplex.IntegrationGeometry.positiveSimplex d t)) :
    ProjectedClasses.IntegrationConstruction.projectedClass X Kᶜ d (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)
      (SimplexCycles.IntegrationConstruction.integralSimplex_relative_cycle X Kᶜ d σ (chartSimplex_faces_avoid e K a r hr hKi σ hcoords)) =
      IntegrationOrientation.Geometry.chartCompactClass e K hK hKs := by
  let iso := AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso (X := X) (Y := TopCat.of (Fin d → ℝ)) e K hK hKs d
  apply iso.toLinearEquiv.injective
  change iso.hom _ = iso.hom (iso.inv _)
  rw [CategoryTheory.Iso.inv_hom_id_apply]
  change (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso (X := X) (Y := TopCat.of (Fin d → ℝ)) e K hK hKs d).hom _ = _
  rw [chartProjectedSimplex_transport (X := X) (Y := TopCat.of (Fin d → ℝ)) e K hK hKs d σ hs
    (chartSimplex_faces_avoid e K a r hr hKi σ hcoords)]
  have hmodel : chartModelSimplex e d σ hs = affineSingularSimplex d a r := by
    apply ((TopCat.of (Fin d → ℝ)).toSSetObjEquiv (op ⦋d⦌)).injective
    apply ContinuousMap.ext
    intro t
    exact hcoords t
  simp only [hmodel]
  exact affineProjectedClass_eq_coordinateCompactClass d a r hr (e '' K)
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (X := X) (Y := TopCat.of (Fin d → ℝ)) e K hK hKs) hKi

end

end OAI.AlgebraicTopology.FundamentalClass.AffineCycle.IntegrationConstruction
