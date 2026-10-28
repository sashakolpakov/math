import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProductOver
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationCharts

/-! # Open Product Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.OpenProductChart.BundleCycles

noncomputable section

/-! The actual Laurent charts of the punctured deformation are open product charts over the complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : E ⟶ X) (U : X.left.AffineZariskiSite)
  (j : Spec (CommRingCat.of (LaurentPolynomial Γ(X.left, U.1))) ⟶ E.left)
  [IsOpenImmersion j]
  (hs : j ≫ f.left = FiberGenericPoint.BundleCycles.laurentProjection Γ(X.left, U.1) ≫ U.2.fromSpec)

abbrev laurentChartAlgebra := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U.1

def laurentChartTotalOverMap : ProductOver.BundleCycles.laurentProductOver (laurentChartAlgebra U) ⟶ E :=
  Over.homMk j (by
    let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U.1
    change j ≫ E.hom = ProductOver.BundleCycles.laurentFiberMap Γ(X.left, U.1) ≫ ProductOver.BundleCycles.complexLaurentOver.hom
    have hb : U.2.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, U.1))) :=
      (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec X.hom U.1 U.2).symm
    calc
      j ≫ E.hom = j ≫ (f.left ≫ X.hom) := congrArg (fun k => j ≫ k) f.w.symm
      _ = (j ≫ f.left) ≫ X.hom := (Category.assoc _ _ _).symm
      _ = (FiberGenericPoint.BundleCycles.laurentProjection Γ(X.left, U.1) ≫ U.2.fromSpec) ≫ X.hom :=
        congrArg (fun k => k ≫ X.hom) hs
      _ = FiberGenericPoint.BundleCycles.laurentProjection Γ(X.left, U.1) ≫ (U.2.fromSpec ≫ X.hom) := Category.assoc _ _ _
      _ = FiberGenericPoint.BundleCycles.laurentProjection Γ(X.left, U.1) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, U.1))) :=
        congrArg (fun k => FiberGenericPoint.BundleCycles.laurentProjection Γ(X.left, U.1) ≫ k) hb
      _ = ProductOver.BundleCycles.laurentFiberMap Γ(X.left, U.1) ≫ ProductOver.BundleCycles.complexLaurentOver.hom :=
        (ProductSquare.BundleCycles.laurentProjection_isPullback ℂ Γ(X.left, U.1)).w)

def laurentOpenProductChart (z : E.left) (hz : z ∈ Set.range j) : Open.ProductChart.BundleCycles.SchemeOpenProductChart f z where
  base := Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (laurentChartAlgebra U)
  total := ProductOver.BundleCycles.laurentProductOver (laurentChartAlgebra U)
  fiber := ProductOver.BundleCycles.complexLaurentOver
  baseMap := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U.1 U.2
  totalMap := laurentChartTotalOverMap f U j hs
  fiberProjection := ProductOver.BundleCycles.laurentFiberOver (laurentChartAlgebra U)
  baseProjection := ProductOver.BundleCycles.laurentProjectionOver (laurentChartAlgebra U)
  baseOpen := inferInstance
  totalOpen := inferInstanceAs (IsOpenImmersion j)
  mem := hz
  square := Over.OverMorphism.ext hs
  product := ProductOver.BundleCycles.laurentProductIsLimit (laurentChartAlgebra U)
  fiberIntegral := inferInstance
  fiberSmooth := inferInstance
  fiberMetrizable := inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.OpenProductChart.BundleCycles
