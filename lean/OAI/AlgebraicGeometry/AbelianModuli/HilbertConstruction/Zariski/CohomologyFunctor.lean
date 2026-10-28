import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyScalars

/-! # Cohomology Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology

noncomputable section

/-! Ext-based Zariski cohomology is a functor to modules over global functions and over any chosen base coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def globalCohomologyModuleObj {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    ModuleCat.{u} Γ(X, ⊤) :=
  ModuleCat.mkOfSMul (CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyAction M n)

def globalCohomologyModuleMap {X : Scheme.{u}} {M N : X.Modules} (n : ℕ) (f : M ⟶ N) :
    globalCohomologyModuleObj M n ⟶ globalCohomologyModuleObj N n :=
  letI := CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyModule M n
  letI := CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyModule N n
  ModuleCat.ofHom (CohomologyScalars.ZariskiCohomology.cohomologyLinearMap n f)

theorem globalCohomologyModuleMap_id {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    globalCohomologyModuleMap n (𝟙 M) = 𝟙 (globalCohomologyModuleObj M n) := by
  apply (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map_injective
  exact (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_id M

theorem globalCohomologyModuleMap_comp {X : Scheme.{u}} {M N P : X.Modules}
    (n : ℕ) (f : M ⟶ N) (g : N ⟶ P) :
    globalCohomologyModuleMap n (f ≫ g) =
      globalCohomologyModuleMap n f ≫ globalCohomologyModuleMap n g := by
  apply (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map_injective
  exact (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_comp f g

def globalCohomologyFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) where
  obj M := globalCohomologyModuleObj M n
  map f := globalCohomologyModuleMap n f
  map_id M := globalCohomologyModuleMap_id M n
  map_comp f g := globalCohomologyModuleMap_comp n f g

instance globalCohomologyFunctor_additive (X : Scheme.{u}) (n : ℕ) :
    (globalCohomologyFunctor X n).Additive where
  map_add := by
    intro M N f g
    apply (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat).map_injective
    exact (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_add

def coefficientCohomologyFunctor {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R :=
  globalCohomologyFunctor X n ⋙ ModuleCat.restrictScalars c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology
