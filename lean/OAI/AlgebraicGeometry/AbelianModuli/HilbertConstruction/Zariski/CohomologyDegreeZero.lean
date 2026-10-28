import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyScalars

/-! # Cohomology Degree Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyDegreeZero.ZariskiCohomology

noncomputable section

/-! The canonical scalar action on degree-zero Zariski cohomology agrees with the actual module structure on global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem globalModuleScalar_app_top {X : Scheme.{u}} (M : X.Modules)
    (r : Γ(X, ⊤)) (x : Γ(M, ⊤)) : (Global.ModuleScalars.globalModuleScalar M r).app ⊤ x = r • x := by
  rw [Global.ModuleScalars.globalModuleScalar_app]
  have hr : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op r = r := by
    rw [Subsingleton.elim (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op (𝟙 _), X.presheaf.map_id]
    rfl
  exact congrArg (fun a : Γ(X, ⊤) ↦ a • x) hr

def hZeroCanonicalLinearEquivGlobalSections {X : Scheme.{u}} (M : X.Modules) :
    letI := CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyModule M 0
    Cohomology.ZariskiCohomology.H M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) := by
  letI := CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyModule M 0
  refine { Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M with map_smul' := ?_ }
  intro r x
  change Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M ((Cohomology.ZariskiCohomology.zariskiFunctor X 0).map (Global.ModuleScalars.globalModuleScalar M r) x) =
    r • Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M x
  exact (Cohomology.ZariskiCohomology.hZeroEquivGlobalSections_naturality (Global.ModuleScalars.globalModuleScalar M r) x).symm.trans
    (globalModuleScalar_app_top M r (Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyDegreeZero.ZariskiCohomology
