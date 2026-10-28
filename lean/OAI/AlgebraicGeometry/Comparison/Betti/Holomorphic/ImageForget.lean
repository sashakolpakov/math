import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModuleForget
import OAI.AlgebraicGeometry.Comparison.Betti.AnalytifiedForm
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicSheafMap

/-! # Image Forget -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ImageForget

noncomputable section

/-! The actual direct image preserves the normalized identification of
holomorphic module sections with the original holomorphic complex terms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def zariskiHolomorphicModuleForgetIso (n : ℕ) :
    (SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).obj
        (AnalytifiedForm.zariskiHolomorphicFormModuleSheaf X n) ≅
      (sheafCompose (Opens.grothendieckTopology X.left)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          ((Algebraic.HolomorphicSheafMap.zariskiHolomorphicSheafComplex X).X n) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (Analytification.Base.analytificationMap X)).mapIso
    (ModuleForget.holomorphicModuleSheafForgetIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n)

theorem zariskiHolomorphicModuleForgetIso_apply (U : X.left.Opens) (n : ℕ)
    (a : DeRhamComplex.forms (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n) :
    (zariskiHolomorphicModuleForgetIso X n).hom.hom.app (op U) a =
      (SheafSections.holomorphicSheafSectionIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
        (Open.AffineIsoEvaluation.analyticOpen X U) n).hom a := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ImageForget
