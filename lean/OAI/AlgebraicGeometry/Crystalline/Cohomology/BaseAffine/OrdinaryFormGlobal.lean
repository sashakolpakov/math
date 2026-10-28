import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification

/-! # Ordinary Form Global -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormGlobal.BaseAffineOrdinaryFormGlobal

noncomputable section

/-! # Actual sheafified de Rham sections on an affine etale chart -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R A
local notation "G" => ModuleCat.restrictScalars (algebraMap R A)

def scalarComponent (n : ℕ) (U : (Spec (CommRingCat.of A)).Opens) :
    (G).obj ((OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n).obj (op U)) ≅
      ((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves R X).obj
        (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n)).obj (op U) :=
  (ModuleCat.restrictScalarsComp'App (algebraMap R A)
    (AlgebraicForms.AlgebraicDeRham.sectionBaseMap A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) U)
    (AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U) (SectionTowers.BaseAffineSectionTowers.sectionBaseMap R A U)
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.formModule R ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)) n)).symm

def rawIso (n : ℕ) : OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n ⋙ G ≅
    DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n :=
  (NatIso.ofComponents (fun U => scalarComponent R A n U.unop) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)) ≪≫ OrdinaryFormBase.OrdinaryFormModulePresheaf.underlyingIso R (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) n

variable (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ R) A]
  [IsScalarTower R (MvPolynomial σ R) A] [Algebra.FormallyEtale (MvPolynomial σ R) A]

def sheafIso (n : ℕ) : (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n ≅
    (sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A))) G).obj
      (NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf (CommRingCat.of A)
        (OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n)) :=
  (presheafToSheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat.{u} R)).mapIso
    (rawIso R A n).symm ≪≫
      NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification.LocalizingPresheafBasis.sheafIsoComp (CommRingCat.of A)
        (OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n)
        (fun a => OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.restriction R A σ a n) G

def globalIso (n : ℕ) : ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op ⊤) ≅
    ModuleCat.of R (DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  (sheafToPresheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat.{u} R) ⋙
    (evaluation _ _).obj (op ⊤)).mapIso (sheafIso R A σ n) ≪≫
      (G).mapIso (tilde.isoTop (R := CommRingCat.of A)
        ((OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf R A n).obj (op ⊤))).symm ≪≫
      (G).mapIso (LinearEquiv.ofBijective (OrdinaryFormSections.BaseAffineOrdinaryFormSections.map R A ⊤ n).hom
        (OrdinaryFormSections.BaseAffineOrdinaryFormSections.top_bijective R A n)).toModuleIso.symm ≪≫
      OrdinaryFormBase.OrdinaryFormModulePresheaf.baseIso R (CommAlgCat.of R A) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormGlobal.BaseAffineOrdinaryFormGlobal
