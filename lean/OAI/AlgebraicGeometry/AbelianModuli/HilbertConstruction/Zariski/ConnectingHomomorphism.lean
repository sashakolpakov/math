import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExact
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnderlyingAdditiveSheafExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor

/-! # Connecting Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.ConnectingHomomorphism.ZariskiCohomology

noncomputable section

/-! The actual Ext connecting homomorphism is compatible with the canonical coefficient action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

def shortComplexGlobalScalar (r : Γ(X, ⊤)) : S ⟶ S where
  τ₁ := Global.ModuleScalars.globalModuleScalar S.X₁ r
  τ₂ := Global.ModuleScalars.globalModuleScalar S.X₂ r
  τ₃ := Global.ModuleScalars.globalModuleScalar S.X₃ r
  comm₁₂ := Global.ModuleScalars.globalModuleScalar_natural r S.f
  comm₂₃ := Global.ModuleScalars.globalModuleScalar_natural r S.g

def cohomologyConnecting (hS : S.ShortExact) (n : ℕ) : Cohomology.ZariskiCohomology.H S.X₃ n →+ Cohomology.ZariskiCohomology.H S.X₁ (n + 1) :=
  Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.δ (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X)) n (n + 1) rfl

theorem cohomologyConnecting_coefficient_smul {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (hS : S.ShortExact) (n : ℕ) (r : R) (x : Cohomology.ZariskiCohomology.H S.X₃ n) :
    cohomologyConnecting hS n ((((CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₃).smul r).hom x) =
      (((CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj S.X₁).smul r).hom (cohomologyConnecting hS n x) :=
  Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.δ_naturality n (n + 1) rfl
    (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X))
    (hS.map_of_exact (UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X))
    ((UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X).mapShortComplex.map (shortComplexGlobalScalar (S := S) (c r))) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.ConnectingHomomorphism.ZariskiCohomology
