import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart

/-! # Product Open Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ProductOpenChart.BundleCycles

noncomputable section

/-! A genuine global product supplies an open product chart at every point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (F X E : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral F.left] [Smooth F.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints F)] (πF : E ⟶ F) (πX : E ⟶ X)
  (hprod : IsLimit (BinaryFan.mk πF πX))

def globalProductOpenChart (z : E.left) : Open.ProductChart.BundleCycles.SchemeOpenProductChart πX z where
  base := X
  total := E
  fiber := F
  baseMap := 𝟙 X
  totalMap := 𝟙 E
  fiberProjection := πF
  baseProjection := πX
  baseOpen := inferInstanceAs (IsOpenImmersion (𝟙 X.left))
  totalOpen := inferInstanceAs (IsOpenImmersion (𝟙 E.left))
  mem := ⟨z, rfl⟩
  square := (Category.id_comp πX).trans (Category.comp_id πX).symm
  product := hprod
  fiberIntegral := inferInstance
  fiberSmooth := inferInstance
  fiberMetrizable := inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ProductOpenChart.BundleCycles
