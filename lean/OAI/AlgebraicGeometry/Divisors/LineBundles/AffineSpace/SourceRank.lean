import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.BundleRankZero
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Source Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace

noncomputable section

/-! The relative dimension of source affine-space charts determines
the dimension of actual integral fiber supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank {E X : Scheme.{0}} (p : E ⟶ X) (r : ℕ) : Prop :=
  ∀ z : E, ∃ (U : Scheme.{0}) (i : U ⟶ X) (ι : Type) (_ : Finite ι)
    (j : AffineSpace ι U ⟶ E), IsOpenImmersion i ∧ IsOpenImmersion j ∧
      z ∈ Set.range j ∧ (AffineSpace ι U ↘ U) ≫ i = j ≫ p ∧ Nat.card ι = r

theorem SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank.forget {E X : Scheme.{0}} {p : E ⟶ X} {r : ℕ}
    (h : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) : SourceBase.BundleCycles.HasAffineSpaceSourceCharts p := by
  intro z
  obtain ⟨U, i, ι, hι, j, hi, hj, hz, hs, _⟩ := h z
  exact ⟨U, i, ι, hι, j, hi, hj, hz, hs⟩

theorem BundleRankZero.Cycles.HasAffineSpaceChartsOfRank.sourceCharts {E X : Scheme.{0}} {p : E ⟶ X} {r : ℕ}
    (h : BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r := by
  intro z
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs, hr⟩ := h (p z)
  obtain ⟨u, hu⟩ := hx
  obtain ⟨a, _, hja⟩ := Scheme.exists_preimage_of_isPullback hs u z hu
  exact ⟨U, i, ι, hι, j, hi, hj, ⟨a, hja⟩, hs.w, hr⟩

theorem SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian X] (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (h : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)) (p ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + r := by
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs, hr⟩ := h (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)
  let := hι
  let := hi
  let := hj
  let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  obtain ⟨a, ha⟩ := hx
  let u := (AffineSpace ι U ↘ U) a
  have hu : i u = x := (congrArg (fun k : AffineSpace ι U ⟶ X => k a) hs).trans
    ((congrArg p ha).trans (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x))
  rw [← hu, ← Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p (AffineSpace ι U ↘ U) i j hs u,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j]
  have he : j ≫ (p ≫ f) = (AffineSpace ι U ↘ U) ≫ (i ≫ f) := by
    rw [← Category.assoc, ← hs, Category.assoc]
  rw [he, CycleGrading.BundleCycles.affineSpaceFiberGenericPoint_dimension, hr, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace
