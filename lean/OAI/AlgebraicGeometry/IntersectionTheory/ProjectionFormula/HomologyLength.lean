import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Homology Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyLength

noncomputable section

/-! For a finite-length middle module, its length is the sum of the
homology length and the lengths of the two adjacent boundary images. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]

theorem quotient_length_add (M : ModuleCat.{u} R) (L : Submodule R M) :
    Module.length R M = Module.length R L + Module.length R (M ⧸ L) :=
  Module.length_eq_add_of_exact L.subtype L.mkQ L.subtype_injective L.mkQ_surjective
    (LinearMap.exact_subtype_mkQ L)

def boundaryEquiv (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.range S.moduleCatToCycles ≃ₗ[R] LinearMap.range S.f.hom := by
  have he : LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).submoduleOf (LinearMap.ker S.g.hom) :=
    LinearMap.range_codRestrict _ _ _
  exact (LinearEquiv.ofEq _ _ he).trans
    (Submodule.submoduleOfEquivOfLe (LinearMap.range_le_ker_iff.mpr
      (ModuleCat.hom_ext_iff.mp S.zero)))

theorem homology_length_ne_top (S : ShortComplex (ModuleCat.{u} R))
    (h : Module.length R S.X₂ ≠ ⊤) : Module.length R S.homology ≠ ⊤ := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.length_eq]
  exact ne_top_of_le_ne_top (ExactLength.kernel_length_ne_top R S.g h)
    (Module.length_le_of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (Submodule.mkQ_surjective _))

theorem middle_length (S : ShortComplex (ModuleCat.{u} R))
    (h : Module.length R S.X₂ ≠ ⊤) :
    ExactLength.rationalLength R S.X₂ = ExactLength.rationalLength R S.homology +
      ExactLength.rationalLength R (.of R (LinearMap.range S.f.hom)) +
      ExactLength.rationalLength R (.of R (LinearMap.range S.g.hom)) := by
  have hk := ExactLength.kernel_length_ne_top R S.g h
  have hl := Module.length_le_of_injective (LinearMap.range S.moduleCatToCycles).subtype
    (Submodule.subtype_injective _)
  have hq := Module.length_le_of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
    (Submodule.mkQ_surjective _)
  have hlen := quotient_length_add R (.of R (LinearMap.ker S.g.hom))
    (LinearMap.range S.moduleCatToCycles)
  have hnat := congrArg (fun a : ℕ∞ => (a.toNat : ℚ)) hlen
  rw [ENat.toNat_add (ne_top_of_le_ne_top hk hl) (ne_top_of_le_ne_top hk hq), Nat.cast_add] at hnat
  have hH : Module.length R S.homology =
      Module.length R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.length_eq
  rw [(boundaryEquiv R S).length_eq, ← hH] at hnat
  rw [ExactLength.rationalLength_eq_kernel_add_range R S.g h]
  unfold ExactLength.rationalLength
  linarith

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologyLength
