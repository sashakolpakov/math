import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenEmbeddingSheafExact

/-! # Scheme Abelian Cohomology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeAbelianCohomology.Construction

noncomputable section

/-! Ordinary abelian sheaves underlying scheme modules and their affine cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Abelian

universe u

def schemeModulesToAbelian (X : Scheme.{u}) :
    X.Modules ⥤ AbelianSheafInjectives.Construction.AbelianSheaves (Scheme.forgetToTop.obj X) :=
  SheafOfModules.toSheaf X.ringCatSheaf

def affineUnderlyingAbelianIso (R : CommRingCat.{u}) (N : (Spec R).Modules) :
    (schemeModulesToAbelian (Spec R)).obj N ≅
      (QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian R (TopCat.of (PrimeSpectrum R))).obj (modulesSpecToSheaf.obj N) :=
  Iso.refl _

def restrictUnderlyingAbelianIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (N : Y.Modules) :
    (schemeModulesToAbelian X).obj (N.restrict f) ≅
      (OpenEmbeddingSheafExact.Construction.openEmbeddingAbelianPullback (f := f.base) f.isOpenEmbedding).obj
        ((schemeModulesToAbelian Y).obj N) :=
  Iso.refl _

variable (R : CommRingCat.{u})

local instance e40SchemeSpecEnoughInjectives :
    EnoughInjectives (AbelianSheafInjectives.Construction.AbelianSheaves (Scheme.forgetToTop.obj (Spec R))) :=
  AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives (Scheme.forgetToTop.obj (Spec R))

local instance e40SchemeSpecHasExt :
    HasExt.{u} (AbelianSheafInjectives.Construction.AbelianSheaves (Scheme.forgetToTop.obj (Spec R))) :=
  hasExt_of_enoughInjectives _

theorem quasicoherent_spec_H_one_subsingleton (N : (Spec R).Modules) [N.IsQuasicoherent] :
    Subsingleton (CategoryTheory.Sheaf.H ((schemeModulesToAbelian (Spec R)).obj N) 1) := by
  exact AffineCohomologyOne.Construction.quasicoherent_affine_H_one_subsingleton R N

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeAbelianCohomology.Construction
