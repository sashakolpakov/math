import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars

/-! # Ordinary Form Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormSheaf.OrdinaryFormSheafComparison

noncomputable section

/-! # The ordinary structure-sheaf module forms give the original base-linear de Rham terms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

def iso (n : ℕ) :
    (NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.functor R X).obj (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R X n) ≅
      (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n :=
  (NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars.objectIso R X
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n)).symm ≪≫
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapIso
        (OrdinaryFormBase.OrdinaryFormModulePresheaf.underlyingIso R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormSheaf.OrdinaryFormSheafComparison
