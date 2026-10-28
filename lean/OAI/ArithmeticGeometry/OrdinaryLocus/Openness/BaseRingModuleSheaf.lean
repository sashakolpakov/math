import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeModuleSheaf
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeAbelianCohomology
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso

/-! # Base Ring Module Sheaf -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseRingModuleSheaf.Construction

noncomputable section

/-! Actual scheme-module Cech complexes over an arbitrary affine base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

def baseRingConstants : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom

def modulesAsBaseRingSheaf : X.Modules ⥤ ModuleSheafInjectives.Construction.ModuleSheaves R (Scheme.forgetToTop.obj X) := by
  let H := ModuleCat.restrictScalars.{u} (baseRingConstants f)
  have hH : (_root_.Opens.grothendieckTopology X).HasSheafCompose H :=
    hasSheafCompose_of_preservesLimitsOfSize (J := _root_.Opens.grothendieckTopology X) (F := H)
  exact SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
      @sheafCompose _ _ _ _ _ _ (_root_.Opens.grothendieckTopology X) H hH

def baseRingUnderlyingAbelianIso (M : X.Modules) :
    (QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian (.of R) (Scheme.forgetToTop.obj X)).obj
      ((modulesAsBaseRingSheaf f).obj M) ≅ (SchemeAbelianCohomology.Construction.schemeModulesToAbelian X).obj M :=
  Iso.refl _

abbrev schemeModuleCechShortComplex (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    ShortComplex (ModuleCat.{u} R) :=
  OpenCechShortComplex.Construction.openModuleCechShortComplex ((modulesAsBaseRingSheaf f).obj M) U

def schemeModuleCechGlobalSectionsEquiv (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) :
    ((modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤) ≃ₗ[R]
      LinearMap.ker (schemeModuleCechShortComplex f M U).f.hom :=
  OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv ((modulesAsBaseRingSheaf f).obj M) U hU

def schemeModuleCechHomologyIso (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (schemeModuleCechShortComplex f M U).homology ≅
      ModuleCat.of R (OpenCechCohomology.Construction.OpenCechH1 ((modulesAsBaseRingSheaf f).obj M) U) :=
  OpenCechHomologyIso.Construction.openModuleCechHomologyIso ((modulesAsBaseRingSheaf f).obj M) U

def baseRingSheafIsoBaseField {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) (M : Y.Modules) :
    (modulesAsBaseRingSheaf g).obj M ≅ (RelativeModuleSheaf.Construction.modulesAsBaseFieldSheaf g).obj M :=
  Iso.refl _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseRingModuleSheaf.Construction
