import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.LargeLimitReflection
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Coefficient Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheaf.CrystallineCoefficientSheaf

noncomputable section

/-!
# Native coefficient lifting preserves the sheaf condition

The prescribed lift of Witt modules only lifts the underlying section
types and restricts scalars along the fixed ring equivalence. The sheaf
condition is preserved, and sheafification of an already-sheaf coefficient
presheaf has the canonical section identification.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "W" => WittVector p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k
abbrev Modules := ModuleCat.{u + 1} (Site.CoefficientRing p k)
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheaf.CrystallineCoefficientSheaf.Modules p k

theorem isSheaf (P : (Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} W)
    (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ E) := by
  have : Limits.ReflectsLimitsOfSize.{u, u + 1} (forget V) :=
    Module.LargeLimitReflection.ModuleLargeLimitReflection.reflectsLimitsOfSize _
  apply Presheaf.isSheaf_of_isSheaf_comp J (P ⋙ E) (forget V)
  apply (isSheaf_iff_isSheaf_of_type J _).mpr
  change Presieve.IsSheaf J ((P ⋙ forget (ModuleCat.{u} W)) ⋙ uliftFunctor.{u + 1})
  apply Presieve.isSheaf_comp_uliftFunctor
  have : Limits.PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} W)) :=
    (ModuleCat.adj W).rightAdjoint_preservesLimits
  exact (isSheaf_iff_isSheaf_of_type J _).mp
    (Presheaf.isSheaf_comp_of_isSheaf J P (forget (ModuleCat.{u} W)) hP)

def liftedSheaf (P : (Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} W)
    (hP : Presheaf.IsSheaf J P) : Sheaf J V := ⟨P ⋙ E, isSheaf p k X P hP⟩

def toSheafIso (P : (Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} W)
    (hP : Presheaf.IsSheaf J P) :
    (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).obj P ≅ liftedSheaf p k X P hP :=
  (sheafificationIso (liftedSheaf p k X P hP)).symm

def presheafIso (P : (Site.Object p k X)ᵒᵖ ⥤ ModuleCat.{u} W)
    (hP : Presheaf.IsSheaf J P) :
    ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).obj P).obj ≅ P ⋙ E :=
  (sheafToPresheaf J V).mapIso (toSheafIso p k X P hP)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheaf.CrystallineCoefficientSheaf
