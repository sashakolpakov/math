import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpaceChartBaseChange

/-! # Open Product Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.OpenProductChart.BundleCycles

noncomputable section

/-! Actual cartesian affine-space bundle charts supply open product
charts over the complex base, including the case of zero fiber rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

section Charts

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : E ⟶ X) (U : Scheme.{0}) (i : U ⟶ X.left)
    [IsOpenImmersion i] (ι : Type) [Finite ι] (j : AffineSpace ι U ⟶ E.left)
    [IsOpenImmersion j] (hs : IsPullback (AffineSpace ι U ↘ U) j i f.left)

def affineChartBaseOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (i ≫ X.hom)

def affineChartBaseMap : affineChartBaseOver U i ⟶ X := Over.homMk i rfl

def affineChartTotalMap : FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceOver ι (affineChartBaseOver U i) ⟶ E :=
  Over.homMk j (by
    rw [FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceOver_structure]
    change j ≫ E.hom = (AffineSpace ι U ↘ U) ≫ (i ≫ X.hom)
    rw [← f.w, ← Category.assoc, ← hs.w, Category.assoc])

omit [IsOpenImmersion i] [Finite ι] [IsOpenImmersion j] in
theorem affineChartTotalMap_square :
    affineChartTotalMap f U i ι j hs ≫ f =
      FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceProjectionOver ι (affineChartBaseOver U i) ≫ affineChartBaseMap U i :=
  Over.OverMorphism.ext hs.w.symm

def affineSpaceOpenProductChart (z : E.left) (hz : z ∈ Set.range j) : Open.ProductChart.BundleCycles.SchemeOpenProductChart f z where
  base := affineChartBaseOver U i
  total := FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceOver ι (affineChartBaseOver U i)
  fiber := FiniteAffine.SpaceOver.BundleCycles.complexFiniteAffineSpaceOver ι
  baseMap := affineChartBaseMap U i
  totalMap := affineChartTotalMap f U i ι j hs
  fiberProjection := FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceFiberOver ι (affineChartBaseOver U i)
  baseProjection := FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceProjectionOver ι (affineChartBaseOver U i)
  baseOpen := inferInstanceAs (IsOpenImmersion i)
  totalOpen := inferInstanceAs (IsOpenImmersion j)
  mem := hz
  square := affineChartTotalMap_square f U i ι j hs
  product := FiniteAffine.SpaceOver.BundleCycles.finiteAffineSpaceProductIsLimit ι (affineChartBaseOver U i)
  fiberIntegral := inferInstance
  fiberSmooth := inferInstance
  fiberMetrizable := inferInstance

end Charts

def affineBundleOpenProductChart {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : E ⟶ X)
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts f.left) (z : E.left) : Open.ProductChart.BundleCycles.SchemeOpenProductChart f z :=
  Classical.choice (show Nonempty (Open.ProductChart.BundleCycles.SchemeOpenProductChart f z) from by
    obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩ := h (f.left z)
    let := hι
    let := hi
    let := hj
    have hr := Scheme.image_preimage_eq_of_isPullback hs Set.univ
    simp only [Set.preimage_univ, Set.image_univ] at hr
    have hz : z ∈ Set.range j := (Set.ext_iff.mp hr z).mpr hx
    exact ⟨affineSpaceOpenProductChart f U i ι j hs z hz⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.OpenProductChart.BundleCycles
