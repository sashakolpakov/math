import OAI.AlgebraicGeometry.Comparison.Betti.Cech.ForgetModules
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechSectionsBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.ComplexHypercohomologyForget

/-! # Sheaf Cech Bicomplex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCechBicomplex

noncomputable section

section

/-! The actual complex-sheaf coefficient functor is compatible with ordinary Čech cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : TopCat.{0})

def complexSheafPresheafForgetIso :
    ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X ≅
      sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ) ⋙
        Cech.ForgetModules.modulePresheafForget :=
  NatIso.ofComponents (fun F => Iso.refl _) (fun f => by
    apply NatTrans.ext
    funext V
    rfl)

variable {ι : Type} (U : ι → Opens X)

def complexSheafCechSectionsFunctorIso :
    (ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive X ⋙ Betti.Sheaf.CechFunctor.sheafCechResolutionFunctor U) ⋙
        Cech.FactorSections.sheafTopSections.mapHomologicalComplex (.up ℕ) ≅
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ) ⋙
        AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U) ⋙
          (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ) := by
  let A := ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive X
  let B := TopCat.Sheaf.forget AddCommGrpCat.{0} X
  let C := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)
  let D := Cech.ForgetModules.modulePresheafForget (X := X)
  let T := (Cech.FactorSections.sheafTopSections (X := X)).mapHomologicalComplex (.up ℕ)
  let E : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
    cechComplexFunctor U
  let N := AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U
  let V := (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)
  exact Functor.associator A (Betti.Sheaf.CechFunctor.sheafCechResolutionFunctor U) T ≪≫
    Functor.isoWhiskerLeft A (Betti.Sheaf.CechSectionsFunctor.sheafCechSectionsFunctorIso U) ≪≫
    (Functor.associator A B E).symm ≪≫
    Functor.isoWhiskerRight (complexSheafPresheafForgetIso X) E ≪≫
    Functor.associator C D E ≪≫
    Functor.isoWhiskerLeft C (Cech.ForgetModules.additiveModuleCechFunctorIso U) ≪≫
    (Functor.associator C N V).symm

end

/-! Both Čech differentials for the original complex sheaves are preserved under coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : TopCat.{0}) {ι : Type} (U : ι → Opens X)

def complexSheafPresheafComplex
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) ℕ) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (.up ℕ)).obj K

def complexSheafOrdinaryCechBicomplex
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) ℕ) :
    HomologicalComplex₂ (ModuleCat.{0} ℂ) (.up ℕ) (.up ℕ) :=
  ((AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj
    (complexSheafPresheafComplex X K)

def complexSheafCechSectionsBicomplexIso
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) ℕ) :
    TotalComplexFunctor.mapBicomplex Cech.FactorSections.sheafTopSections
        (Betti.Sheaf.CechAugmentation.sheafCechBicomplex U
          (((ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive X).mapHomologicalComplex (.up ℕ)).obj K)) ≅
      TotalComplexFunctor.mapBicomplex (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})
        (complexSheafOrdinaryCechBicomplex X U K) := by
  have : ((ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive X ⋙ Betti.Sheaf.CechFunctor.sheafCechResolutionFunctor U) ⋙
      Cech.FactorSections.sheafTopSections.mapHomologicalComplex (.up ℕ)).Additive :=
    Functor.additive_of_iso (complexSheafCechSectionsFunctorIso X U).symm
  exact (NatIso.mapHomologicalComplex (complexSheafCechSectionsFunctorIso X U) (.up ℕ)).app K

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCechBicomplex
