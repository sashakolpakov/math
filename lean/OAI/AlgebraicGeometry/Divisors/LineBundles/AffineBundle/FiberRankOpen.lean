import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen

/-! # Fiber Rank Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen.Cycles

noncomputable section

section

/-! Actual fiber rank is preserved on open cartesian charts, and can
be computed on a projective chart of the same integral ambient fiber. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundleFiberRank_openSquare {E X E' U : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian E']
    (p : E ⟶ X) (q : E' ⟶ U) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : q ≫ i = j ≫ p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (u : U) :
    FiberRank.Cycles.affineBundleFiberRank p f (i u) = FiberRank.Cycles.affineBundleFiberRank q (i ≫ f) u := by
  unfold FiberRank.Cycles.affineBundleFiberRank
  rw [← Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q i j hs u,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i]
  have he : j ≫ (p ≫ f) = q ≫ (i ≫ f) := by rw [← Category.assoc, ← hs, Category.assoc]
  rw [he]

theorem affineBundleFiberRank_commonOpen {E A B X U : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian B]
    [AlgebraicGeometry.IsNoetherian U]
    (p : E ⟶ X) (q : A ⟶ X) (t : B ⟶ U)
    [GeometricallyIntegral p] [GeometricallyIntegral q] [GeometricallyIntegral t]
    (j : A ⟶ E) (k : B ⟶ E) (i : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion i]
    (hj : j ≫ p = q) (hk : t ≫ i = k ≫ p)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (ht : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank t r) (u : U) :
    FiberRank.Cycles.affineBundleFiberRank q f (i u) = r := by
  have ha : j (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint q (i u)) = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) :=
    Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q (𝟙 X) j (by rw [Category.comp_id, hj]) (i u)
  have hb := Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p t i k hk u
  have H := congrArg (fun z : E =>
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm z) (p ≫ f)) (ha.trans hb.symm)
  rw [ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion k] at H
  have hjf : j ≫ (p ≫ f) = q ≫ f := by rw [← Category.assoc, hj]
  have hkf : k ≫ (p ≫ f) = t ≫ (i ≫ f) := by rw [← Category.assoc, ← hk, Category.assoc]
  rw [hjf, hkf, AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension t (i ≫ f) r ht] at H
  unfold FiberRank.Cycles.affineBundleFiberRank
  rw [H, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i]
  omega

end

/-! The rank strata of an actual affine-space bundle are open and
closed, and their actual pullbacks have the specified constant rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p) (r : ℕ)

def affineBundleRankOpen : X.Opens :=
  ⟨{x | FiberRank.Cycles.affineBundleFiberRank p f x = r}, (FiberRank.Cycles.affineBundleFiberRank_locallyConstant p f h).isOpen_fiber r⟩

theorem affineBundleRankOpen_isClosed : IsClosed (affineBundleRankOpen p f h r : Set X) :=
  (FiberRank.Cycles.affineBundleFiberRank_locallyConstant p f h).isClosed_fiber r

instance affineBundleRankOpen_isNoetherian :
    AlgebraicGeometry.IsNoetherian (affineBundleRankOpen p f h r).toScheme :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (affineBundleRankOpen p f h r).ι

instance affineBundleRankOpen_isClosedImmersion : IsClosedImmersion (affineBundleRankOpen p f h r).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact affineBundleRankOpen_isClosed p f h r)

theorem affineBundleRankOpen_mem (x : X) :
    x ∈ affineBundleRankOpen p f h (FiberRank.Cycles.affineBundleFiberRank p f x) := rfl

theorem affineBundleRankOpen_disjoint (s : ℕ) (hrs : r ≠ s) :
    Disjoint (affineBundleRankOpen p f h r) (affineBundleRankOpen p f h s) := by
  apply TopologicalSpace.Opens.coe_disjoint.mp
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hrs (hx.symm.trans hy)

variable [AlgebraicGeometry.IsNoetherian E]

instance affineBundleRankPullback_isNoetherian :
    AlgebraicGeometry.IsNoetherian (pullback p (affineBundleRankOpen p f h r).ι : Scheme) :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (pullback.fst p (affineBundleRankOpen p f h r).ι)

theorem affineBundleRankOpen_charts :
    AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank (pullback.snd p (affineBundleRankOpen p f h r).ι) r := by
  let i := (affineBundleRankOpen p f h r).ι
  let : AlgebraicGeometry.IsNoetherian (affineBundleRankOpen p f h r).toScheme := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  let : AlgebraicGeometry.IsNoetherian (pullback p i : Scheme) := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (pullback.fst p i)
  apply FiberRank.Cycles.affineBundle_hasChartsOfRank_of_fiberRank (pullback.snd p i) (i ≫ f) (h.baseChange i) r
  intro u
  rw [← affineBundleFiberRank_openSquare p (pullback.snd p i) i (pullback.fst p i)
    (pullback.condition.symm) f u]
  exact u.property

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen.Cycles
