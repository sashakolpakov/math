import OAI.Analysis.DifferentialForms.Manifold.OpenD
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Topology.Sheaves.Presheaf

/-! # Presheaf -/

namespace OAI.Analysis.DifferentialForms.Manifold.Presheaf

noncomputable section

/-!
# The presheaf of smooth complex-valued real differential forms

The objects are the actual open-domain forms of `Forms.Open`. Restrictions are
their pointwise restrictions. Exterior differentiation gives a natural morphism
between successive presheaves and its square is zero. The sheaf condition is
proved separately from genuine open-cover gluing.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The usual pointwise additive structure on module-valued presheaves. -/
instance smoothFormPresheafCategoryPreadditive :
    Preadditive (TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of E)) :=
  inferInstanceAs (Preadditive ((Opens (TopCat.of E))ᵒᵖ ⥤ ModuleCat.{u} ℂ))

/-- Smooth degree-n forms and their actual restriction maps, as a module presheaf. -/
def smoothFormPresheaf (n : ℕ) : TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of E) where
  obj U := ModuleCat.of ℂ (OpenD.SmoothOpenForm (unop U) n)
  map h := ModuleCat.ofHom (OpenD.SmoothOpenForm.restrict (CategoryTheory.leOfHom h.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact OpenD.SmoothOpenForm.restrict_refl form
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    apply OpenD.SmoothOpenForm.ext
    intro x
    rfl

@[simp] theorem smoothFormPresheaf_obj (n : ℕ) (U : Opens E) :
    (smoothFormPresheaf E n).obj (op U) = ModuleCat.of ℂ (OpenD.SmoothOpenForm U n) := rfl

@[simp] theorem smoothFormPresheaf_map (n : ℕ) {U V : Opens E} (h : V ≤ U) :
    (smoothFormPresheaf E n).map (homOfLE h).op =
      ModuleCat.ofHom (OpenD.SmoothOpenForm.restrict h) := rfl

/-- Exterior differentiation is natural with respect to open restriction. -/
def smoothFormPresheafD (n : ℕ) :
    smoothFormPresheaf E n ⟶ smoothFormPresheaf E (n + 1) where
  app U := ModuleCat.ofHom OpenD.SmoothOpenForm.d
  naturality U V h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact (OpenD.SmoothOpenForm.restrict_d (CategoryTheory.leOfHom h.unop) form).symm

@[simp] theorem smoothFormPresheafD_app (n : ℕ) (U : Opens E) :
    (smoothFormPresheafD E n).app (op U) =
      ModuleCat.ofHom (OpenD.SmoothOpenForm.d (U := U) (n := n)) := rfl

/-- The presheaf differential squares to zero as a natural transformation. -/
theorem smoothFormPresheafD_squared (n : ℕ) :
    smoothFormPresheafD E n ≫ smoothFormPresheafD E (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact OpenD.SmoothOpenForm.d_squared form

end

end OAI.Analysis.DifferentialForms.Manifold.Presheaf
