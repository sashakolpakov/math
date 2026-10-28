import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! # Module Section Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleSectionIsomorphisms

noncomputable section

/-! A map of actual module sheaves that is bijective on every
section module is an actual sheaf isomorphism. -/

open _root_.CategoryTheory

universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}

theorem moduleSheaf_isIso_of_section_bijective (f : M ⟶ N)
    (h : ∀ U : Cᵒᵖ, Function.Bijective (f.val.app U)) : IsIso f := by
  let : ∀ U : Cᵒᵖ, IsIso (f.val.app U) :=
    fun U => (ConcreteCategory.isIso_iff_bijective (f.val.app U)).mpr (h U)
  let e : M.val ≅ N.val := PresheafOfModules.isoMk (fun U => asIso (f.val.app U))
    (fun {_ _} g => f.val.naturality g)
  have he : e.hom = f.val := rfl
  let : IsIso f.val := he ▸ (inferInstanceAs (IsIso e.hom))
  let : IsIso ((SheafOfModules.forget R).map f) := inferInstanceAs (IsIso f.val)
  exact isIso_of_reflects_iso f (SheafOfModules.forget R)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleSectionIsomorphisms
