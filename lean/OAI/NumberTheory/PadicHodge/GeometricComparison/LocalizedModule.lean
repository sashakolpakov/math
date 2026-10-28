import Mathlib.Algebra.Category.ModuleCat.Localization

/-! # Localized Module -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizedModule.LocalizedModuleIso

noncomputable section

/-! Two localizations of a module are isomorphic compatibly with their defining maps. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (S : Submonoid R)
  {M N N' : ModuleCat.{u} R} (f : M ⟶ N) (g : M ⟶ N')
  [IsLocalizedModule S f.hom] [IsLocalizedModule S g.hom]

include S in
theorem exists_iso : ∃ e : N ≅ N', f ≫ e.hom = g := by
  refine ⟨(IsLocalizedModule.linearEquiv S f.hom g.hom).toModuleIso, ?_⟩
  apply ModuleCat.hom_ext
  exact LinearMap.ext (IsLocalizedModule.linearEquiv_apply S f.hom g.hom)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizedModule.LocalizedModuleIso
