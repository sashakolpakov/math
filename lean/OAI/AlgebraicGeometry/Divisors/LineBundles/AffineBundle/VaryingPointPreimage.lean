import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ClopenPointPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen

/-! # Varying Point Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.VaryingPointPreimage.Cycles

noncomputable section

/-! Every finite point cycle on an actual affine-space bundle admits a
preimage in all Chow grades, including when the relative rank varies. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem affineBundlePointChow_preimage {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p)
    (β : E →₀ ℚ) : ∃ z : X →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) = Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d β := by
  classical
  let ι := Set.range (FiberRank.Cycles.affineBundleFiberRank p f)
  let : Fintype ι := (FiberRank.Cycles.affineBundleFiberRank_finite p f h).fintype
  let U (r : ι) : Scheme := (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).toScheme
  let i (r : ι) : U r ⟶ X := (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι
  let V (r : ι) : Scheme := pullback p (i r)
  let q (r : ι) : V r ⟶ U r := pullback.snd p (i r)
  let j (r : ι) : V r ⟶ E := pullback.fst p (i r)
  let : ∀ r, AlgebraicGeometry.IsNoetherian (U r) := fun r => inferInstanceAs
    (AlgebraicGeometry.IsNoetherian (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).toScheme)
  let : ∀ r, IsOpenImmersion (i r) := fun r => inferInstanceAs
    (IsOpenImmersion (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι)
  let : ∀ r, IsClosedImmersion (i r) := fun r => inferInstanceAs
    (IsClosedImmersion (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι)
  let : ∀ r, AlgebraicGeometry.IsNoetherian (V r) := fun r => inferInstanceAs
    (AlgebraicGeometry.IsNoetherian (pullback p (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι : Scheme))
  let : ∀ r, Smooth (q r) := fun r => inferInstanceAs (Smooth (pullback.snd p (i r)))
  let : ∀ r, GeometricallyIntegral (q r) := fun r => inferInstanceAs (GeometricallyIntegral (pullback.snd p (i r)))
  let : ∀ r, IsOpenImmersion (j r) := fun r => inferInstanceAs (IsOpenImmersion (pullback.fst p (i r)))
  let : ∀ r, IsClosedImmersion (j r) := fun r => inferInstanceAs (IsClosedImmersion (pullback.fst p (i r)))
  have hc : ∀ x : X, ∃! r : ι, x ∈ Set.range (i r) := by
    intro x
    refine ⟨⟨FiberRank.Cycles.affineBundleFiberRank p f x, ⟨x, rfl⟩⟩, ⟨⟨x, rfl⟩, rfl⟩, ?_⟩
    rintro r ⟨u, rfl⟩
    exact Subtype.ext u.property.symm
  exact ClopenPointPreimage.Cycles.affineBundlePointChow_preimage_of_clopen p f U V q i j
    (fun r => (IsPullback.of_hasPullback p (i r)).flip) Subtype.val
    (fun r => FiberRankOpen.Cycles.affineBundleRankOpen_charts p f h r.val) hc β

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.VaryingPointPreimage.Cycles
