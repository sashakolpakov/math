import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PowerPushforwardVanishing
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex

/-! # Chow Power Vanishing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowPowerVanishing.BundleCycles

noncomputable section

/-! The lower triangular vanishing formulas for proper bundle
projections: fewer line-bundle intersections than the relative fiber
dimension still push to zero. All maps are the constructed geometric maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem dimensionComponentInclusion_support {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : X →₀ ℚ) (x : X)
    (hx : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z) x ≠ 0) : z x ≠ 0 := by
  have hr : x ∈ Set.range (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) := by
    by_contra hn
    exact hx (Finsupp.mapDomain_of_notMem_range _ _ hn)
  obtain ⟨a, rfl⟩ := hr
  change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z) a.val ≠ 0 at hx
  rw [Open.CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply f d _ a] at hx
  exact hx

theorem integralFiberCycleExtension_image_dimension
    {E X : Scheme.{0}} (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (x : E) (hx : Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p x)) f = d := by
  have hr : x ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) := by
    by_contra hn
    exact hx (Finsupp.mapDomain_of_notMem_range _ _ hn)
  obtain ⟨y, rfl⟩ := hr
  rw [Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection]
  change Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z)
    (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p y) ≠ 0 at hx
  rw [Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective p)] at hx
  have hy : y ∈ Set.range (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) := by
    by_contra hn
    exact hx (Finsupp.mapDomain_of_notMem_range _ _ hn)
  obtain ⟨a, rfl⟩ := hy
  exact a.property

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

theorem affineSpaceSourceChowExtension_power_pushforward_zero
    (d s n : ℕ) (hds : d < s) (hd : d + r = s + n) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f s
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) s n
        (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r h d a))) = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv_pointClass]
  apply LineBundle.PowerPushforwardVanishing.Cycles.separatedLineBundleChowPower_pushforward_zero p f L d s n hds
  intro x hx
  exact (integralFiberCycleExtension_image_dimension p f d z x
    (dimensionComponentInclusion_support (p ≫ f) (s + n) _ x hx)).le

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowPowerVanishing.BundleCycles
