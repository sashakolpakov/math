import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRingAction

/-! # Cohomology Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyScalars.ZariskiCohomology

noncomputable section

/-! Actual global functions act canonically on Ext-based Zariski cohomology, and actual module morphisms induce linear maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def cohomologyEndRingHom {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    End M →+* End ((Cohomology.ZariskiCohomology.zariskiFunctor X n).obj M) where
  toFun := (Cohomology.ZariskiCohomology.zariskiFunctor X n).map
  map_one' := (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_id M
  map_mul' f g := (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_comp g f
  map_zero' := (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_zero M M
  map_add' _ _ := (Cohomology.ZariskiCohomology.zariskiFunctor X n).map_add

def globalSectionsCohomologyAction {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* End ((Cohomology.ZariskiCohomology.zariskiFunctor X n).obj M) :=
  (cohomologyEndRingHom M n).comp (Global.ScalarRingAction.globalModuleScalarRingHom M)

@[reducible]
def globalSectionsCohomologyModule {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    Module Γ(X, ⊤) (Cohomology.ZariskiCohomology.H M n) := by
  change Module Γ(X, ⊤) (ModuleCat.mkOfSMul' (globalSectionsCohomologyAction M n))
  infer_instance

theorem globalSectionsCohomologyModule_smul {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    (r : Γ(X, ⊤)) (x : Cohomology.ZariskiCohomology.H M n) :
    letI := globalSectionsCohomologyModule M n
    r • x = (Cohomology.ZariskiCohomology.zariskiFunctor X n).map (Global.ModuleScalars.globalModuleScalar M r) x := rfl

def cohomologyLinearMap {X : Scheme.{u}} {M N : X.Modules} (n : ℕ) (f : M ⟶ N) :
    letI := globalSectionsCohomologyModule M n
    letI := globalSectionsCohomologyModule N n
    Cohomology.ZariskiCohomology.H M n →ₗ[Γ(X, ⊤)] Cohomology.ZariskiCohomology.H N n := by
  letI := globalSectionsCohomologyModule M n
  letI := globalSectionsCohomologyModule N n
  refine { toFun := (Cohomology.ZariskiCohomology.zariskiFunctor X n).map f
           map_add' := ((Cohomology.ZariskiCohomology.zariskiFunctor X n).map f).hom.map_add
           map_smul' := ?_ }
  intro r x
  change (Cohomology.ZariskiCohomology.zariskiFunctor X n).map f ((Cohomology.ZariskiCohomology.zariskiFunctor X n).map (Global.ModuleScalars.globalModuleScalar M r) x) =
    (Cohomology.ZariskiCohomology.zariskiFunctor X n).map (Global.ModuleScalars.globalModuleScalar N r) ((Cohomology.ZariskiCohomology.zariskiFunctor X n).map f x)
  have h := congrArg (Cohomology.ZariskiCohomology.zariskiFunctor X n).map (Global.ModuleScalars.globalModuleScalar_natural r f)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyScalars.ZariskiCohomology
