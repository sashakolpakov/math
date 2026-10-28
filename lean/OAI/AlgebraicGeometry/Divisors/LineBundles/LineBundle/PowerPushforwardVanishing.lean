import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CyclePower
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPushforwardBound

/-! # Power Pushforward Vanishing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PowerPushforwardVanishing.Cycles

noncomputable section

/-! Proper pushforward of iterated line-bundle intersections
vanishes whenever the remaining cycle dimension exceeds the dimensions
of the original supports' images. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (p : X ⟶ Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] [LocallyOfFiniteType (p ≫ f)]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem lineBundleCyclePower_pushforward_zero (b d n : ℕ) (hbd : b < d)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + n) →₀ ℚ)
    (hz : ∀ x, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) (d + n) z x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p x)) f ≤ b) :
    DimensionPointPushforward.BundleCycles.dimensionPointPushforward p f d (CyclePower.Cycles.lineBundleCyclePower L (p ≫ f) d n z) = 0 := by
  apply DimensionPushforwardBound.BundleCycles.dimensionPointPushforward_zero_of_image_dimension
  intro x hx
  rw [CyclePower.Cycles.lineBundleCyclePower_forget] at hx
  exact (CyclePower.Cycles.lineBundlePointPower_image_dimension_bound L p f b n _ hz x hx).trans_lt hbd

theorem separatedLineBundleChowPower_pushforward_zero [X.IsSeparated] [Y.IsSeparated] [IsProper p]
    (b d n : ℕ) (hbd : b < d) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + n) →₀ ℚ)
    (hz : ∀ x, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) (d + n) z x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p x)) f ≤ b) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d n (DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + n) z)) = 0 := by
  rw [CyclePower.Cycles.separatedLineBundleChowPower_cycle, Proper.ChowNe.BundleCycles.properChowPushforward_cycle,
    lineBundleCyclePower_pushforward_zero p f L b d n hbd z hz, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PowerPushforwardVanishing.Cycles
