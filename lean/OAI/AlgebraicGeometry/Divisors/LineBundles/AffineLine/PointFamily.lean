import OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePoints
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PointPairContinuity

/-! # Point Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointFamily.BundleCycles

noncomputable section

/-! The actual complex points of an affine line form a continuous
parameter family over the original complex point space. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions
open scoped MonoidalCategory

def affineLineFirstOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : OverProduct.BundleCycles.affineLineOver X ⟶ X :=
  Over.homMk (Charts.BundleCycles.affineLineProjection X.left) rfl

theorem affineLineProductOverIso_fst (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (OverProduct.BundleCycles.affineLineProductOverIso X).hom ≫ fst X OverProduct.BundleCycles.complexAffineLineOver = affineLineFirstOver X :=
  Over.OverMorphism.ext (OverProduct.BundleCycles.affineLineProductSchemeIso_fst X)

def affineLinePointFamily (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ℂ → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OverProduct.BundleCycles.affineLineOver X) :=
  fun z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OverProduct.BundleCycles.affineLineProductOverIso X).inv
    ((CycleClass.Thom.Scheme.PointProduct.Constructions.schemePointProductHomeomorph X OverProduct.BundleCycles.complexAffineLineOver).symm (z.1, ComplexAffinePoints.BundleCycles.complexAffineLinePoint z.2))

theorem affineLinePointFamily_continuous (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Continuous (affineLinePointFamily X) := by
  let g : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ℂ, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ OverProduct.BundleCycles.complexAffineLineOver)) :=
    ⟨fun z => (CycleClass.Thom.Scheme.PointProduct.Constructions.schemePointProductHomeomorph X OverProduct.BundleCycles.complexAffineLineOver).symm (z.1, ComplexAffinePoints.BundleCycles.complexAffineLinePoint z.2),
      Scheme.PointPairContinuity.BundleCycles.schemePointPair_continuous_comp X OverProduct.BundleCycles.complexAffineLineOver Prod.fst
        (fun z => ComplexAffinePoints.BundleCycles.complexAffineLinePoint z.2) continuous_fst
        (ComplexAffinePoints.BundleCycles.complexAffineLinePoint_continuous.comp continuous_snd)⟩
  let h : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ OverProduct.BundleCycles.complexAffineLineOver), ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OverProduct.BundleCycles.affineLineOver X)) :=
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OverProduct.BundleCycles.affineLineProductOverIso X).inv,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (OverProduct.BundleCycles.affineLineProductOverIso X).inv⟩
  exact (h.comp g).continuous

theorem affineLinePointFamily_projection (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ℂ) :
    affineLinePointFamily X z ≫ affineLineFirstOver X = z.1 := by
  change (lift z.1 (ComplexAffinePoints.BundleCycles.complexAffineLinePoint z.2) ≫ (OverProduct.BundleCycles.affineLineProductOverIso X).inv) ≫ _ = _
  rw [← affineLineProductOverIso_fst, Category.assoc, Iso.inv_hom_id_assoc, lift_fst]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointFamily.BundleCycles
