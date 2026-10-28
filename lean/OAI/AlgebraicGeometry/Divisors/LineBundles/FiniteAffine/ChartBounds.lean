import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.AffineSchemeGraph

/-! # Chart Bounds -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.ChartBounds.BundleCycles

noncomputable section

/-! A finite map supplies a genuine surjective polynomial presentation and a compact coordinate bound on an actual ambient neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.AffineSchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} (k : S ⟶ N) [IsFinite k.left] (B : N.left.Opens)

instance finiteAffineSource_isAffine [IsAffine (OpenChart.BundleCycles.finiteAffineBase B).left] : IsAffine (OpenChart.BundleCycles.finiteAffineSource k B).left :=
  isAffine_of_isAffineHom (OpenChart.BundleCycles.finiteAffineMap k B).left

def finiteAffineChartAnalyticImage (V : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineBase B))) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B) '' (V : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineBase B))),
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (OpenChart.BundleCycles.finiteAffineBaseInclusion B)).isOpenMap _ V.isOpen⟩

theorem finiteAffineChartAnalyticImage_subset (V : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineBase B))) :
    (finiteAffineChartAnalyticImage B V : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B)) := by
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

variable [LocallyOfFiniteType N.hom] [IsAffine (OpenChart.BundleCycles.finiteAffineBase B).left]

local instance finiteAffineChartBoundsLFT : LocallyOfFiniteType (OpenChart.BundleCycles.finiteAffineBase B).hom :=
  inferInstanceAs (LocallyOfFiniteType (B.ι ≫ N.hom))

theorem finiteAffineChart_exists_bounded_graph (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OpenChart.BundleCycles.finiteAffineBase B)) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ((OpenChart.BundleCycles.finiteAffineSource k B).left, ⊤))
      (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (K : Set (Fin d → ℂ)),
      Function.Surjective f ∧ IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap (OpenChart.BundleCycles.finiteAffineMap k B) f).left ∧
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B) x ∈ U ∧
      (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B)) ∧
      IsCompact K ∧
      ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) y) ∈ U →
        CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K := by
  obtain ⟨d, f, V, K, hf, hscheme, hx, hK, _, hb⟩ := CycleClass.Thom.Finite.AffineSchemeGraph.Constructions.exists_bounded_finite_graph (OpenChart.BundleCycles.finiteAffineMap k B) x
  refine ⟨d, f, finiteAffineChartAnalyticImage B V, K, hf, hscheme,
    ⟨x, hx, rfl⟩, finiteAffineChartAnalyticImage_subset B V, hK, ?_⟩
  intro y hy
  obtain ⟨v, hv, he⟩ := hy
  have hs : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) y) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineBaseInclusion B) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineMap k B) y) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (OpenChart.BundleCycles.finiteAffineSourceInclusion k B) k y).symm.trans
      ((congrArg (fun m => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map m y) (OpenChart.BundleCycles.finiteAffineChart_square k B)).trans
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (OpenChart.BundleCycles.finiteAffineMap k B) (OpenChart.BundleCycles.finiteAffineBaseInclusion B) y))
  have hvy := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (OpenChart.BundleCycles.finiteAffineBaseInclusion B)).injective (he.trans hs)
  have hyV : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenChart.BundleCycles.finiteAffineMap k B) y ∈ V := hvy ▸ hv
  exact (hb ⟨⟨y, hyV⟩, rfl⟩).2

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.ChartBounds.BundleCycles
