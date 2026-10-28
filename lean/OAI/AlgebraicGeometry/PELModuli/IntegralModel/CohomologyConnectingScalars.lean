import OAI.AlgebraicGeometry.SheafCohomology.AffineH
import OAI.AlgebraicGeometry.SheafCohomology.Exact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge

/-! # Cohomology Connecting Scalars -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyConnectingScalars

noncomputable section

/-! Connecting homomorphisms in actual sheaf cohomology are linear for
the canonical action of the global functions of the base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.AffineH.Projective OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge
universe u

variable {X B : Scheme.{u}} (f : X ⟶ B)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)

/-- Multiplication on the three terms is a morphism of short complexes. -/
def shortComplexGlobalSmul (r : Γ(X, ⊤)) : S ⟶ S where
  τ₁ := SheafCohomology.AffineH.Projective.globalSmulHom S.X₁ r
  τ₂ := SheafCohomology.AffineH.Projective.globalSmulHom S.X₂ r
  τ₃ := SheafCohomology.AffineH.Projective.globalSmulHom S.X₃ r
  comm₁₂ := SheafCohomology.AffineH.Projective.globalSmulHom_naturality S.f r
  comm₂₃ := SheafCohomology.AffineH.Projective.globalSmulHom_naturality S.g r

/-- The usual Ext connecting homomorphism, with its original coefficients. -/
def cohomologyConnecting (n : ℕ) : SheafCohomology.AffineH.Projective.H S.X₃ n →+ SheafCohomology.AffineH.Projective.H S.X₁ (n + 1) :=
  CategoryTheory.Sheaf.H.δ (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n (n + 1) rfl

private theorem zariskiMap_apply {M N : X.Modules} (a : M ⟶ N) (n : ℕ) (x : SheafCohomology.AffineH.Projective.H M n) :
    (SheafCohomology.AffineH.Projective.zariskiFunctor X n).map a x =
      CategoryTheory.Sheaf.H.map ((SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X).map a) n x := rfl

theorem cohomologyConnecting_smul (n : ℕ) (r : Γ(X, ⊤)) (x : SheafCohomology.AffineH.Projective.H S.X₃ n) :
    letI := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule S.X₃ n
    letI := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule S.X₁ (n + 1)
    cohomologyConnecting hS n (r • x) = r • cohomologyConnecting hS n x := by
  let := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule S.X₃ n
  let := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule S.X₁ (n + 1)
  rw [SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule_smul, SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule_smul,
    zariskiMap_apply, zariskiMap_apply]
  have h := CategoryTheory.Sheaf.H.δ_naturality
    n (n + 1) rfl
    (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X))
    (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X))
    ((SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X).mapShortComplex.map
      (shortComplexGlobalSmul (S := S) r)) x
  exact h

/-- The connecting map retains the canonical action of the base ring. -/
def baseCohomologyConnectingLinearMap (n : ℕ) :
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₃ n
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₁ (n + 1)
    SheafCohomology.AffineH.Projective.H S.X₃ n →ₗ[Γ(B, ⊤)] SheafCohomology.AffineH.Projective.H S.X₁ (n + 1) := by
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₃ n
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₁ (n + 1)
  exact { cohomologyConnecting hS n with
    map_smul' := fun r x => cohomologyConnecting_smul hS n (f.appTop r) x }

/-- A coefficient morphism induces a linear map over the original base. -/
def baseCohomologyLinearMap {M N : X.Modules} (n : ℕ) (a : M ⟶ N) :
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f N n
    SheafCohomology.AffineH.Projective.H M n →ₗ[Γ(B, ⊤)] SheafCohomology.AffineH.Projective.H N n := by
  letI := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule M n
  letI := SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule N n
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f N n
  exact { (SheafCohomology.AffineH.Projective.cohomologyLinearMap n a).toAddHom with
    map_smul' := fun r x => (SheafCohomology.AffineH.Projective.cohomologyLinearMap n a).map_smul (f.appTop r) x }

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyConnectingScalars
