import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartMaps
import Mathlib.CategoryTheory.Yoneda

/-! # Chart Representability -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartRepresentability

noncomputable section

/-! Each finite-free quotient chart is corepresented by its polynomial coordinate algebra. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (k l : ℕ)

/-- The functor of quotient-chart points, with the scalar extension of their defining kernels. -/
def grassmannChartFunctor : CommAlgCat.{u} R ⥤ Type u where
  obj A := Charts.GrassmannChart A (Fin l → A) k
  map f := TypeCat.ofHom (Charts.GrassmannChart.map f.hom.toRingHom)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro c
    exact Charts.GrassmannChart.map_id c
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro c
    exact Charts.GrassmannChart.map_comp f.hom.toRingHom g.hom.toRingHom c

/-- The chart coordinate algebra has one variable for each entry of the rectangular matrix. -/
def grassmannChartCoordinateAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (MvPolynomial (Fin k × Fin l) R)

/-- The precise universal property of the polynomial coordinate algebra of one chart. -/
def grassmannChartCorepresentable :
    (grassmannChartFunctor R k l).CorepresentableBy (grassmannChartCoordinateAlgebra R k l) where
  homEquiv :=
    { toFun := fun f => PolynomialCoordinates.grassmannChartPolynomialEquiv f.hom
      invFun := fun c => CommAlgCat.ofHom (PolynomialCoordinates.grassmannChartPolynomialEquiv.symm c)
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        exact PolynomialCoordinates.grassmannChartPolynomialEquiv.symm_apply_apply f.hom
      right_inv := fun c => PolynomialCoordinates.grassmannChartPolynomialEquiv.apply_symm_apply c }
  homEquiv_comp g f := Charts.GrassmannChart.polynomialEquiv_naturality g.hom f.hom

/-- Every chart point is obtained from a unique map out of the chart coordinate algebra. -/
theorem grassmannChart_existsUnique_parameter (A : CommAlgCat.{u} R)
    (c : Charts.GrassmannChart A (Fin l → A) k) :
    ∃! f : grassmannChartCoordinateAlgebra R k l ⟶ A,
      (grassmannChartCorepresentable R k l).homEquiv f = c := by
  let e := (grassmannChartCorepresentable R k l).homEquiv (Y := A)
  refine ⟨e.symm c, e.apply_symm_apply c, ?_⟩
  intro f hf
  exact e.injective (hf.trans (e.apply_symm_apply c).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartRepresentability
