import OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsGluing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.LargeLimitReflection

/-! # Functions Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSheaf.CrystallineFunctionsSheaf

noncomputable section

/-!
# Actual ambient crystalline functions already satisfy the sheaf condition

Every native covering sieve contains a unit-ideal principal cover.
Fraction gluing gives existence on that cover, while separation on
all native pullback covers extends the gluing to the whole sieve.
The resulting theorem concerns the original ambient-function presheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "Values" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSeparation.CrystallineFunctionsSeparation.values p k X

theorem values_isSheaf : Presieve.IsSheaf J Values := by
  intro Q S hS
  let s := FunctionsSeparation.CrystallineFunctionsSeparation.coefficients p k X S
  have hs := FunctionsSeparation.CrystallineFunctionsSeparation.coefficients_span p k X S hS
  let R := CrystallinePrincipal.Covers.CrystallinePrincipalCovers.presieve p k X Q s Subtype.val
  have hgen : Presieve.IsSheafFor Values (Sieve.generate R).arrows :=
    (Presieve.isSheafFor_iff_generate R).mp (FunctionsGluing.CrystallineFunctionsGluing.principal_isSheafFor p k X Q s hs)
  have hle : Sieve.generate R ≤ S := by
    apply (Sieve.generate_le_iff _ _).mpr
    intro P f hf
    obtain ⟨i⟩ := hf
    exact i.property
  have hcover : Sieve.generate R ∈ J Q :=
    CrystallinePrincipal.Covers.CrystallinePrincipalCovers.covering_mem p k X Q s Subtype.val
      (by simpa only [Subtype.range_val] using hs)
  exact Presieve.isSheafFor_subsieve_aux Values hle hgen
    (fun {P} {f} _ => FunctionsSeparation.CrystallineFunctionsSeparation.separated p k X ((Sieve.generate R).pullback f)
      ((J).pullback_stable f hcover))

theorem functions_isSheaf : Presheaf.IsSheaf J (Site.functions p k X) := by
  have : Limits.ReflectsLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} (WittVector p k))) :=
    Module.LargeLimitReflection.ModuleLargeLimitReflection.reflectsLimitsOfSize _
  apply Presheaf.isSheaf_of_isSheaf_comp J (Site.functions p k X)
    (forget (ModuleCat.{u} (WittVector p k)))
  exact (isSheaf_iff_isSheaf_of_type J Values).mpr (values_isSheaf p k X)

def functionsSheaf : Sheaf J (ModuleCat.{u} (WittVector p k)) :=
  ⟨Site.functions p k X, functions_isSheaf p k X⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FunctionsSheaf.CrystallineFunctionsSheaf
