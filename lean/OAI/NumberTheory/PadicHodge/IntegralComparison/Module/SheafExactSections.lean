import Mathlib

/-! # Sheaf Exact Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafExactSections

noncomputable section

/-!
# IntegralComparison: objectwise exactness implies exactness of module sheaves

Exactness on every section module makes the underlying presheaf complex
exact. Exact sheafification and its counit then give exactness of the
original sheaf complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R]

theorem presheaf_exact (S : ShortComplex (Cᵒᵖ ⥤ ModuleCat.{w} R))
    (h : ∀ U : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ (ModuleCat.{w} R)).obj U)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, Functor.isZero_iff]
  intro U
  exact IsZero.of_iso ((S.map _).exact_iff_isZero_homology.mp (h U))
    (S.mapHomologyIso ((evaluation Cᵒᵖ (ModuleCat.{w} R)).obj U)).symm

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]

def sheafificationIso (S : ShortComplex (Sheaf J (ModuleCat.{w} R))) :
    ((S.map (sheafToPresheaf J (ModuleCat.{w} R))).map (presheafToSheaf J (ModuleCat.{w} R))) ≅ S :=
  ShortComplex.isoMk
    (CategoryTheory.sheafificationIso S.X₁).symm
    (CategoryTheory.sheafificationIso S.X₂).symm
    (CategoryTheory.sheafificationIso S.X₃).symm
    ((sheafificationNatIso J (ModuleCat.{w} R)).inv.naturality S.f).symm
    ((sheafificationNatIso J (ModuleCat.{w} R)).inv.naturality S.g).symm

theorem exact_of_sections (S : ShortComplex (Sheaf J (ModuleCat.{w} R)))
    (h : ∀ (U : C) (x : S.X₂.obj.obj (op U)), S.g.hom.app (op U) x = 0 →
      ∃ y : S.X₁.obj.obj (op U), S.f.hom.app (op U) y = x) : S.Exact := by
  have hP : (S.map (sheafToPresheaf J (ModuleCat.{w} R))).Exact := by
    apply presheaf_exact R
    intro U
    exact (ShortComplex.moduleCat_exact_iff _).mpr (h U.unop)
  exact ShortComplex.exact_of_iso (SheafExactSections.sheafificationIso R J S) (hP.map (presheafToSheaf J (ModuleCat.{w} R)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafExactSections
