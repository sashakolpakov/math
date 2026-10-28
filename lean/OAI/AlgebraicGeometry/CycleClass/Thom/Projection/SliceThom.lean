import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.ProjectionSliceThomPoint
import OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PreimageNeighborhood

/-! # Slice Thom -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.LocalCoefficient

/-! Every point of the actual finite slice fiber has coefficient one in the actual sliced immersion Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.ProjectionSliceThomPoint.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PreimageNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions.LocalCoefficients OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductSimpleZero.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E G W : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
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

variable [Nonempty (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P)]

theorem exists_sliceThomClass_localPoint
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    (hfin : (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)).Finite)
    (hip : ∀ y, (i y).1 = f x →
      Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y))
    (e : ((Fin c → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (c + d) → ℂ))
    (z : SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) :
    ∃ (V : Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ))) (hzV : z.val ∈ V)
      (hIso : ∀ a : V, a.val ∈ SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i) → a.val = z.val),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ))) (V : Set _))
        (Thom.Finite.PointCohomology.Constructions.LocalCoefficients.isolationMapsTo (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) V
          ⟨z.val, hzV⟩ (fun a ha => Subtype.ext (hIso a ha)))
        (2 * (c + d)) (SliceRestriction.Constructions.sliceThomClass P i hi hii he hp) =
          Open.ProductSimpleZero.Constructions.Class.localPointClass (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e V ⟨z.val, hzV⟩ := by
  let F := SliceFiberEquiv.Constructions.Support.ambientSliceProduct P (TopCat.of (Fin d → ℂ))
  obtain ⟨y, hy⟩ := z.property
  have hT : Set.range i ⊆ Set.range f ×ˢ Set.univ := by
    rintro a ⟨b, rfl⟩
    exact ⟨hr ⟨b, rfl⟩, trivial⟩
  have h0 : z.val.1 = HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P :=
    (SliceFiberEquiv.Constructions.Support.sliceSupport_bound P (TopCat.of (Fin d → ℂ)) (Set.range i) Set.univ hT z.property).1
  have hxy : (i y).1 = f x := by
    have h := congrArg Prod.fst hy
    change (i y).1 = Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P z.val.1 at h
    rwa [h0, Normal.SliceDifferential.Constructions.normalSliceAmbient_origin] at h
  have hz : z.val = (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) :=
    Prod.ext h0 (congrArg Prod.snd hy).symm
  obtain ⟨Q, hQ, hQa, _⟩ := FixedNormalPair.Constructions.exists_analytic_normalPair i hi hii he.isEmbedding (c + d) hp y
  have hq : F z.val ∈ Q.openNeighborhood := hy ▸ Q.point_mem_neighborhood
  obtain ⟨V, hzV, hV, hIso⟩ := Thom.Finite.PreimageNeighborhood.Constructions.exists_isolating_open F F.hom.continuous (Set.range i)
    hfin z.val Q.openNeighborhood hq
  let hIso' : ∀ a : V, a.val ∈ SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i) → a.val = z.val :=
    fun a ha => hIso a.val a.property ha
  refine ⟨V, hzV, hIso', ?_⟩
  have hs := SliceRestriction.Constructions.sliceThomClass_local P i hi hii he hp y Q hQ V hV ⟨z.val, hzV⟩
    (fun a ha => Subtype.ext (hIso' a ha))
  exact hs.trans (ProjectionSliceThomPoint.Constructions.sliceToPair_Thom_pointClass P Q hP hPi hQ hQa
    (hi.mdifferentiable (show (ω : ℕ∞ω) ≠ 0 by simp) y) hxy hr (hip y hxy) e V
    ⟨z.val, hzV⟩ hz hV (fun a ha => Subtype.ext (hIso' a ha)))

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.LocalCoefficient

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.Integration

/-! Integration of the actual sliced immersion Thom class counts the actual finite projection fiber. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.LocalCoefficient OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions.Product OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductSimpleZero.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E G W : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
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

variable [Nonempty (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P)]

theorem integrate_sliceThomClass
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (hT : Set.range i ⊆ Set.range f ×ˢ K)
    [Fintype (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i))]
    (hip : ∀ y, (i y).1 = f x →
      Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y))
    (e : ((Fin c → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (c + d) → ℂ)) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P)) {HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P} K hK
      (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i))
      (SliceFiberEquiv.Constructions.Support.sliceSupport_bound P (TopCat.of (Fin d → ℂ)) (Set.range i) K hT)
      (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm (SliceRestriction.Constructions.sliceThomClass P i hi hii he hp) =
        (Fintype.card (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) : ℚ) •
          HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOriginRelativeDualClass (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos) := by
  classical
  let T := SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)
  have hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f := by
    rintro a ⟨y, rfl⟩
    exact (hT ⟨y, rfl⟩).1
  choose V hzV hIso hclass using
    (fun z : T => LocalCoefficient.exists_sliceThomClass_localPoint P i hi hii he hp hP hPi hr (Set.toFinite T) hip e z)
  let := Open.FinitePointProjection.Constructions.Product.openProductCharted (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e
  let := Open.FinitePointProjection.Constructions.openProductManifold (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e
  have hc := Open.FinitePointProjection.Constructions.openFiniteClass_project_of_local (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e
    (Metric.mem_ball_self P.radius_pos) K hK T
    (SliceFiberEquiv.Constructions.Support.sliceSupport_bound P (TopCat.of (Fin d → ℂ)) (Set.range i) K hT) V hzV hIso
    (SliceRestriction.Constructions.sliceThomClass P i hi hii he hp) (fun _ => (1 : ℚ)) (by
      intro z
      simpa only [one_smul, Open.ProductSimpleZero.Constructions.Class.localPointClass] using hclass z)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hc

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.Integration

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.ProjectedNormalRestriction

/-! Actual supported projection of a finite immersion has its fiber-cardinality Thom normalization on each base normal chart. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.Integration OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceFiberEquiv.Constructions.Support
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Slice.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegreeNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E G W : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
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

variable [Nonempty (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P)]

theorem projectedThomClass_normalRestriction
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (hT : Set.range i ⊆ Set.range f ×ˢ K)
    [Fintype (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i))]
    (hip : ∀ y, (i y).1 = f x →
      Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y))
    (e : ((Fin c → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (c + d) → ℂ)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood)
      (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) P.relativeComplement
        (Set.range f)ᶜ from fun _ hy => hy) (2 * c)
      (Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of N) (Set.range f) K hK (Set.range i) hT
        (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm
        (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (c + d) hp)) =
      (Fintype.card (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) : ℚ) • P.rationalClassFin := by
  apply Normal.SliceDetection.Constructions.normalSlice_pullback_injective P (2 * c)
  rw [map_smul, Normal.Slice.Constructions.Class.normalSlice_class]
  let a := Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii he (c + d) hp
  let r := Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of N) (Set.range f) K hK (Set.range i) hT
    (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm a
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (Normal.SliceDetection.Constructions.normalSliceMap P)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) P.neighborhood) (Normal.SliceDetection.Constructions.normalSliceMapsTo P)
      (B := P.relativeComplement) (C := (Set.range f)ᶜ) (fun _ hy => hy) (2 * c)) r
  have hn := Supported.ProjectionDegreeNaturality.Constructions.projectAt_natural d (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) {HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P} (Set.range f)
    (SliceFiberEquiv.Constructions.Support.sliceSupport P (TopCat.of (Fin d → ℂ)) (Set.range i)) (Set.range i) K hK
    (SliceFiberEquiv.Constructions.Support.sliceSupport_bound P (TopCat.of (Fin d → ℂ)) (Set.range i) K hT) hT
    (SliceFiberEquiv.Constructions.Support.ambientSlice_mapsTo P) (fun _ hy => hy) (2 * c) (2 * (c + d)) (Nat.mul_add 2 c d).symm a
  exact hc.trans (hn.symm.trans (Integration.integrate_sliceThomClass P i hi hii he hp hP hPi K hK hT hip e))

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceThom.Constructions.ProjectedNormalRestriction

end

end OAI
