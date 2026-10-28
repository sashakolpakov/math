import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.OpenProductChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationFlat

/-! # Product Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.ProductCharts.BundleCycles

noncomputable section

/-! Every point of the actual punctured deformation has a constructed open product chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.left.IdealSheafData)

def puncturedDeformationOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ X.hom))

def puncturedProjectionOver : puncturedDeformationOver X I ⟶ X :=
  Over.homMk (DeformationCharts.BundleCycles.puncturedDeformationProjection I) (Category.assoc _ _ _)

def puncturedOpenProductChart (z : (puncturedDeformationOver X I).left) :
    Open.ProductChart.BundleCycles.SchemeOpenProductChart (puncturedProjectionOver X I) z :=
  Classical.choice (show Nonempty (Open.ProductChart.BundleCycles.SchemeOpenProductChart (puncturedProjectionOver X I) z) from by
    obtain ⟨U, hz⟩ := DeformationCharts.BundleCycles.puncturedLaurentChart_covers I z
    exact ⟨@Laurent.OpenProductChart.BundleCycles.laurentOpenProductChart (puncturedDeformationOver X I) X
      (puncturedProjectionOver X I) U (DeformationCharts.BundleCycles.puncturedLaurentChart I U)
      (DeformationCharts.BundleCycles.puncturedLaurentChart_openImmersion I U) (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U) z hz⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.ProductCharts.BundleCycles
