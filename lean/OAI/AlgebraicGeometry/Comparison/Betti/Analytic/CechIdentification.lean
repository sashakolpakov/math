import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechCover
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap

/-! # Cech Identification -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification

noncomputable section

/-! The Zariski direct-image smooth complex has the actual manifold Čech total on the analytic cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def zariskiSmoothPresheafDirectImageIso :
    Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X ≅
      Cech.PushforwardFunctor.presheafDirectImageComplex (Analytification.Base.analytificationMap X)
        (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex_d]
    change 𝟙 _ ≫ (Cech.PushforwardFunctor.presheafDirectImage (Analytification.Base.analytificationMap X)).map
      ((Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).d i (i + 1)) = _
    rw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d]
    simp only [Iso.refl_hom, Category.id_comp]
    rfl)

def zariskiSmoothCechTotalIso {ι : Type} (U : ι → X.left.Opens) :
    AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalComplex U (Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X) ≅
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RegularSmoothness.NativeModel X) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i)) :=
  (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalFunctor U).mapIso (zariskiSmoothPresheafDirectImageIso X) ≪≫
    Cech.PushforwardFunctor.cechPushforwardTotalIso (Analytification.Base.analytificationMap X) U
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ≪≫
    AlgebraicTopology.DeRham.Comparison.ManifoldCechAugmentationBridge.manifoldPresheafCechTotalIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification
