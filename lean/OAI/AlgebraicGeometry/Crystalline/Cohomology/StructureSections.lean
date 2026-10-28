import OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSheaf

/-! # Structure Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.StructureSections.CrystallineStructureSections

noncomputable section

/-!
# Concrete sections of the original crystalline structure sheaf

The universe-lifted ambient functions remain a sheaf. The canonical
sheafification isomorphism therefore identifies the original native
structure sheaf, naturally on every object and morphism, with those
actual ambient Witt modules.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
abbrev Modules := ModuleCat.{u + 1} (Site.CoefficientRing p k)
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.StructureSections.CrystallineStructureSections.Modules p k

theorem functionsLarge_isSheaf : Presheaf.IsSheaf J (Site.functionsLarge p k X) := by
  have : Limits.ReflectsLimitsOfSize.{u, u + 1} (forget V) :=
    Module.LargeLimitReflection.ModuleLargeLimitReflection.reflectsLimitsOfSize _
  apply Presheaf.isSheaf_of_isSheaf_comp J (Site.functionsLarge p k X) (forget V)
  apply (isSheaf_iff_isSheaf_of_type J _).mpr
  change Presieve.IsSheaf J (FunctionsSeparation.CrystallineFunctionsSeparation.values p k X ⋙ uliftFunctor.{u + 1})
  exact Presieve.isSheaf_comp_uliftFunctor J (FunctionsSheaf.CrystallineFunctionsSheaf.values_isSheaf p k X)

def functionsSheaf : Sheaf J V := ⟨Site.functionsLarge p k X, functionsLarge_isSheaf p k X⟩

def structureSheafIso : Site.structureSheaf p k X ≅ functionsSheaf p k X :=
  (sheafificationIso (functionsSheaf p k X)).symm

def structurePresheafIso : (Site.structureSheaf p k X).obj ≅ Site.functionsLarge p k X :=
  (sheafToPresheaf J V).mapIso (structureSheafIso p k X)

def sectionIso (Q : Site.Object p k X) :
    (Site.structureSheaf p k X).obj.obj (op Q) ≅ (Site.functionsLarge p k X).obj (op Q) :=
  (structurePresheafIso p k X).app (op Q)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.StructureSections.CrystallineStructureSections
