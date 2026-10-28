import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointFamily
import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

/-! # Point Homotopy -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointHomotopy.BundleCycles

noncomputable section

/-! The actual zero and one point sections of the relative affine line
are homotopic through its continuous complex parameter family. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

def affineLinePointSection (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) :
    TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⟶ TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (OverProduct.BundleCycles.affineLineOver X)) :=
  TopCat.ofHom ⟨fun x => PointFamily.BundleCycles.affineLinePointFamily X (x, a),
    (PointFamily.BundleCycles.affineLinePointFamily_continuous X).comp (continuous_id.prodMk continuous_const)⟩

def affineLinePointSectionsHomotopy (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    TopCat.Homotopy (affineLinePointSection X 0) (affineLinePointSection X 1) where
  toFun z := PointFamily.BundleCycles.affineLinePointFamily X (z.2, ((z.1 : ℝ) : ℂ))
  continuous_toFun := (PointFamily.BundleCycles.affineLinePointFamily_continuous X).comp
    (continuous_snd.prodMk (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)))
  map_zero_left x := by
    change PointFamily.BundleCycles.affineLinePointFamily X (x, ((0 : ℝ) : ℂ)) = PointFamily.BundleCycles.affineLinePointFamily X (x, 0)
    rw [Complex.ofReal_zero]
  map_one_left x := by
    change PointFamily.BundleCycles.affineLinePointFamily X (x, ((1 : ℝ) : ℂ)) = PointFamily.BundleCycles.affineLinePointFamily X (x, 1)
    rw [Complex.ofReal_one]

theorem affineLinePointSections_cohomology_eq (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    {R : Type} [Ring R] (M : ModuleCat.{0} R) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M (affineLinePointSection X 0) n =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M (affineLinePointSection X 1) n :=
  AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyPullback_eq M (affineLinePointSectionsHomotopy X) n

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointHomotopy.BundleCycles
