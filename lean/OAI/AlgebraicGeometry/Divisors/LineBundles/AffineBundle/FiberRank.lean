import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceRank
import Mathlib.Topology.LocallyConstant.Basic

/-! # Fiber Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRank.Cycles

noncomputable section

section

/-! The fiber rank of an actual affine-space bundle is locally constant.
It is defined by geometric support dimensions, and every chart computes it. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def affineBundleFiberRank (x : X) : ℕ :=
  Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)) (p ≫ f) -
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f

variable [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f]

theorem affineBundleFiberRank_openChart {U : Scheme.{0}} (i : U ⟶ X) [IsOpenImmersion i]
    (ι : Type) [Finite ι] (j : AffineSpace ι U ⟶ E) [IsOpenImmersion j]
    (hs : (AffineSpace ι U ↘ U) ≫ i = j ≫ p) (u : U) :
    affineBundleFiberRank p f (i u) = Nat.card ι := by
  let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  unfold affineBundleFiberRank
  rw [← Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p (AffineSpace ι U ↘ U) i j hs u,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j]
  have he : j ≫ (p ≫ f) = (AffineSpace ι U ↘ U) ≫ (i ≫ f) := by
    rw [← Category.assoc, ← hs, Category.assoc]
  rw [he, LineBundles.AffineSpace.CycleGrading.BundleCycles.affineSpaceFiberGenericPoint_dimension, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i]
  omega

theorem affineBundleFiberRank_locallyConstant (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) :
    IsLocallyConstant (affineBundleFiberRank p f) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h x
  let := hι
  let := hi
  let := hj
  refine ⟨i.opensRange, i.opensRange.isOpen, hx, ?_⟩
  obtain ⟨u, rfl⟩ := hx
  rintro y ⟨v, rfl⟩
  rw [affineBundleFiberRank_openChart p f i ι j hs.w v,
    affineBundleFiberRank_openChart p f i ι j hs.w u]

theorem affineBundleFiberRank_eq_of_rank (r : ℕ) (h : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (x : X) :
    affineBundleFiberRank p f x = r := by
  unfold affineBundleFiberRank
  rw [LineBundles.AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension p f r h]
  omega

theorem affineBundle_hasChartsOfRank_of_fiberRank (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) (r : ℕ)
    (hr : ∀ x : X, affineBundleFiberRank p f x = r) : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r := by
  intro x
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h x
  let := hι
  let := hi
  let := hj
  refine ⟨U, i, ι, hι, j, hi, hj, hx, hs, ?_⟩
  obtain ⟨u, rfl⟩ := hx
  exact (affineBundleFiberRank_openChart p f i ι j hs.w u).symm.trans (hr (i u))

theorem affineBundleFiberRank_finite (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) :
    (Set.range (affineBundleFiberRank p f)).Finite :=
  (affineBundleFiberRank_locallyConstant p f h).range_finite

end

/-! The generic fiber point adds the actual local fiber rank, without
requiring constant rank across different components. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem affineBundleFiberGenericPoint_dimension_varying {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian X] (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)) (p ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + affineBundleFiberRank p f x := by
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h x
  let := hι
  let := hi
  let := hj
  let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  obtain ⟨u, rfl⟩ := hx
  rw [affineBundleFiberRank_openChart p f i ι j hs.w u,
    ← Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p (AffineSpace ι U ↘ U) i j hs.w u,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j]
  have he : j ≫ (p ≫ f) = (AffineSpace ι U ↘ U) ≫ (i ≫ f) := by
    rw [← Category.assoc, ← hs.w, Category.assoc]
  rw [he, LineBundles.AffineSpace.CycleGrading.BundleCycles.affineSpaceFiberGenericPoint_dimension, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRank.Cycles
