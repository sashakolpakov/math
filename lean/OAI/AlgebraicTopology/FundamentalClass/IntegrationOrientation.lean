import OAI.AlgebraicTopology.FundamentalClass.LocalSimplex
import OAI.AlgebraicTopology.FundamentalClass.RealSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental
import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Integration Orientation -/

namespace OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation

noncomputable section

/-! Integration: orientations as coherent, geometrically normalized local generators.
The local coordinates send the positively ordered affine simplex to the
locally constant chart sign. A global class is constructed by finite gluing;
no global fundamental class or integration identity is an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

namespace Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def positiveCoordinateClass (d : ℕ) (x : Fin d → ℝ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin d → ℝ)) x d :=
  (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).inv (LocalSimplex.IntegrationGeometry.positiveLocalClass d)

def coordinateCompactClass (d : ℕ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) K d :=
  AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of (Fin d → ℝ))
    (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupport_subset_closedBall (Fin d → ℝ) K hK) d
    ((AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.closedBallOriginHomologyIso (Fin d → ℝ) (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius (Fin d → ℝ) K hK)
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius_pos (Fin d → ℝ) K hK).le d).inv (LocalSimplex.IntegrationGeometry.positiveLocalClass d))

theorem coordinateCompactClass_atPoint (d : ℕ) (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (x : Fin d → ℝ) (hx : x ∈ K) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) K x hx d
      (coordinateCompactClass d K hK) = positiveCoordinateClass d x := by
  unfold coordinateCompactClass
  rw [AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint_apply]
  apply (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).toLinearEquiv.injective
  change (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).hom
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.closedBallPointHomologyMap (Fin d → ℝ) (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius (Fin d → ℝ) K hK)
        x (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupport_subset_closedBall (Fin d → ℝ) K hK hx) d
        ((AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.closedBallOriginHomologyIso (Fin d → ℝ) (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius (Fin d → ℝ) K hK)
          (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius_pos (Fin d → ℝ) K hK).le d).inv (LocalSimplex.IntegrationGeometry.positiveLocalClass d))) =
    (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).hom
      ((AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x d).inv (LocalSimplex.IntegrationGeometry.positiveLocalClass d))
  rw [Iso.inv_hom_id_apply]
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.closedBallPointHomologyMap_translation (Fin d → ℝ)
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius (Fin d → ℝ) K hK)
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius_pos (Fin d → ℝ) K hK).le x
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupport_subset_closedBall (Fin d → ℝ) K hK hx) d)
    ((AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.closedBallOriginHomologyIso (Fin d → ℝ) (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius (Fin d → ℝ) K hK)
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius_pos (Fin d → ℝ) K hK).le d).inv (LocalSimplex.IntegrationGeometry.positiveLocalClass d))
  exact h.trans (Iso.inv_hom_id_apply
    (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.closedBallOriginHomologyIso (Fin d → ℝ) (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius (Fin d → ℝ) K hK)
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.compactSupportRadius_pos (Fin d → ℝ) K hK).le d) (LocalSimplex.IntegrationGeometry.positiveLocalClass d))

variable {d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]

def chartLocalClass (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (x : M) (hx : x ∈ e.source) : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of M) x d :=
  (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
    (X := TopCat.of M) (Y := TopCat.of (Fin d → ℝ)) e x hx d).inv
    (positiveCoordinateClass d (e x))

def chartCompactClass (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K d :=
  (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso (X := TopCat.of M) (Y := TopCat.of (Fin d → ℝ))
    e K hK hKs d).inv
    (coordinateCompactClass d (e '' K)
      (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (X := TopCat.of M)
        (Y := TopCat.of (Fin d → ℝ)) e K hK hKs))

theorem chartCompactClass_atPoint (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) (x : M) (hx : x ∈ K) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx d (chartCompactClass e K hK hKs) =
      chartLocalClass e x (hKs hx) := by
  let q := AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso (X := TopCat.of M)
    (Y := TopCat.of (Fin d → ℝ)) e K hK hKs d
  let l := AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (X := TopCat.of M) (Y := TopCat.of (Fin d → ℝ))
    e x (hKs hx) d
  apply l.toLinearEquiv.injective
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso_toPoint (X := TopCat.of M) (Y := TopCat.of (Fin d → ℝ))
      e K hK hKs d x hx) (chartCompactClass e K hK hKs)
  change AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (e '' K) (e x) _ d
      (q.hom (q.inv (coordinateCompactClass d (e '' K)
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (X := TopCat.of M)
          (Y := TopCat.of (Fin d → ℝ)) e K hK hKs)))) =
    l.hom (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx d (chartCompactClass e K hK hKs)) at h
  rw [Iso.inv_hom_id_apply, coordinateCompactClass_atPoint] at h
  exact h.symm.trans (Iso.inv_hom_id_apply l _).symm

end Geometry

/-- A real orientation: local integral homology coordinates with locally
constant chart signs, normalized on actual positively ordered affine simplices.
The compatibility condition concerns only local topology, never integration. -/
structure Orientation (d : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M] [T2Space M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] where
  localCoordinate : ∀ x : M, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of M) x d ≃ₗ[ℤ] ℤ
  chartSign : ∀ center : M, LocallyConstant (chartAt (Fin d → ℝ) center).source ℤˣ
  chart_normalization : ∀ (center x : M) (hx : x ∈ (chartAt (Fin d → ℝ) center).source),
    localCoordinate x (Geometry.chartLocalClass (chartAt (Fin d → ℝ) center) x hx) =
      (chartSign center ⟨x, hx⟩ : ℤ)

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [T2Space M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

def Orientation.localClass (o : Orientation d M) (x : M) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of M) x d := (o.localCoordinate x).symm 1

theorem Orientation.localClass_normalization (o : Orientation d M) (x : M) :
    o.localCoordinate x (o.localClass x) = 1 := (o.localCoordinate x).apply_symm_apply _

theorem Orientation.localClass_ne_zero (o : Orientation d M) (x : M) :
    o.localClass x ≠ 0 := by
  intro h
  have hn := o.localClass_normalization x
  rw [h, map_zero] at hn
  exact zero_ne_one hn

theorem Orientation.localClass_generates (o : Orientation d M) (x : M)
    (a : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of M) x d) :
    ∃! k : ℤ, k • o.localClass x = a := by
  refine ⟨o.localCoordinate x a, ?_, ?_⟩
  · apply (o.localCoordinate x).injective
    simp [Orientation.localClass]
  · intro k hk
    have h := congrArg (o.localCoordinate x) hk
    simpa [Orientation.localClass] using h

theorem Orientation.signed_chartClass (o : Orientation d M) (center x : M)
    (hx : x ∈ (chartAt (Fin d → ℝ) center).source) :
    (o.chartSign center ⟨x, hx⟩ : ℤ) •
      Geometry.chartLocalClass (chartAt (Fin d → ℝ) center) x hx = o.localClass x := by
  apply (o.localCoordinate x).injective
  rw [map_zsmul, o.chart_normalization, o.localClass_normalization]
  rcases Int.units_eq_one_or (o.chartSign center ⟨x, hx⟩) with h | h <;> simp [h]

variable [CompactSpace M]

theorem Orientation.localClass_lift_neighborhood (o : Orientation d M) (x : M) :
    ∃ C : Set M, IsCompact C ∧ C ∈ 𝓝 x ∧
      ∃ a : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) C d,
        ∀ y (hy : y ∈ C), AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) C y hy d a = o.localClass y := by
  let e := chartAt (Fin d → ℝ) x
  let sx : ℤˣ := o.chartSign x ⟨x, mem_chart_source (Fin d → ℝ) x⟩
  let V : Set e.source := {y | o.chartSign x y = sx}
  have hV : IsOpen V := (o.chartSign x).isLocallyConstant.isOpen_fiber sx
  let U : Set M := Subtype.val '' V
  have hU : IsOpen U := e.open_source.isOpenMap_subtype_val V hV
  have hxU : x ∈ U := ⟨⟨x, mem_chart_source (Fin d → ℝ) x⟩, rfl, rfl⟩
  obtain ⟨C, hC, hxC, hCU⟩ := exists_compact_subset hU hxU
  have hCs : C ⊆ e.source := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := hCU hy
    exact z.property
  have hsign (y : M) (hy : y ∈ C) : o.chartSign x ⟨y, hCs hy⟩ = sx := by
    obtain ⟨z, hz, rfl⟩ := hCU hy
    exact hz
  refine ⟨C, hC, mem_interior_iff_mem_nhds.mp hxC,
    (sx : ℤ) • Geometry.chartCompactClass e C hC hCs, ?_⟩
  intro y hy
  rw [map_zsmul, Geometry.chartCompactClass_atPoint, ← hsign y hy]
  exact o.signed_chartClass x y (hCs hy)

theorem Orientation.exists_wholeSupportClass (o : Orientation d M) :
    ∃ a : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) Set.univ d,
      ∀ x (hx : x ∈ (Set.univ : Set M)),
        AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) Set.univ x hx d a = o.localClass x := by
  choose C hC hCx a ha using o.localClass_lift_neighborhood
  obtain ⟨s, _, hs⟩ := isCompact_univ.elim_nhds_subcover_nhdsSet (fun x _ => hCx x)
  have hcover : (Set.univ : Set M) = ⋃ x ∈ s, C x :=
    Set.Subset.antisymm (subset_of_mem_nhdsSet hs) (Set.subset_univ _)
  rw [hcover]
  apply AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.finiteSupportUnion_glue (TopCat.of M) s C d (fun x _ => hC x)
    (fun _ _ K hK _ => RealSupport.IntegrationGeometry.realManifold_compactSupport_eq_zero_of_pointwise d K hK)
    o.localClass
  intro x _
  exact ⟨a x, ha x⟩

/-- The integral fundamental class, obtained by gluing local classes and
identifying whole-support relative homology with ordinary singular homology. -/
def integralFundamentalClass (o : Orientation d M) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d :=
  (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso (TopCat.of M) d).hom o.exists_wholeSupportClass.choose

theorem integralFundamentalClass_atPoint (o : Orientation d M) (x : M) :
    HomologicalComplex.homologyMap
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) d
      (integralFundamentalClass o) = o.localClass x := by
  unfold integralFundamentalClass
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso_hom_toPoint (TopCat.of M) d x)
    o.exists_wholeSupportClass.choose
  exact h.trans (o.exists_wholeSupportClass.choose_spec x (Set.mem_univ x))

theorem integralFundamentalClass_normalization (o : Orientation d M) (x : M) :
    o.localCoordinate x
      (HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) d
        (integralFundamentalClass o)) = 1 := by
  rw [integralFundamentalClass_atPoint, o.localClass_normalization]

/-- Local normalization determines the global fundamental class uniquely. -/
theorem integralFundamentalClass_unique (o : Orientation d M)
    (a : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology d)
    (ha : ∀ x : M, HomologicalComplex.homologyMap
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) ({x}ᶜ : Set M)) d a = o.localClass x) :
    a = integralFundamentalClass o := by
  let q := AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso (TopCat.of M) d
  apply q.toLinearEquiv.symm.injective
  apply RealSupport.IntegrationGeometry.realManifold_compactSupport_point_ext d Set.univ isCompact_univ
  intro x hx
  have hleft := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso_inv_toPoint (TopCat.of M) d x) a
  have hright := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso_inv_toPoint (TopCat.of M) d x) (integralFundamentalClass o)
  exact hleft.trans ((ha x).trans ((integralFundamentalClass_atPoint o x).symm.trans hright.symm))

theorem integralFundamentalClass_ne_zero (o : Orientation d M) [Nonempty M] :
    integralFundamentalClass o ≠ 0 := by
  intro h
  have hn := integralFundamentalClass_normalization o (Classical.choice ‹Nonempty M›)
  rw [h, map_zero, map_zero] at hn
  exact zero_ne_one hn

/-- The same geometrically normalized class, with coefficients extended to ℂ. -/
def fundamentalClass (o : Orientation d M) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (TopCat.of M)).homology d :=
  Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) d (integralFundamentalClass o)

end

end OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation
