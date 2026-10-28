import Mathlib.RingTheory.Length
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Exact Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

noncomputable section

/-! Length identities for exact module sequences, with finiteness proved
before converting ENat lengths to rational numbers. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]

def rationalLength (M : ModuleCat.{u} R) : ℚ := (Module.length R M).toNat

theorem kernel_range_length {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Module.length R M = Module.length R (LinearMap.ker f.hom) +
      Module.length R (LinearMap.range f.hom) := by
  apply Module.length_eq_add_of_exact (LinearMap.ker f.hom).subtype f.hom.rangeRestrict
    (Submodule.subtype_injective _) f.hom.surjective_rangeRestrict
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext y.property

theorem range_length_ne_top {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : Module.length R M ≠ ⊤) : Module.length R (LinearMap.range f.hom) ≠ ⊤ := by
  exact ne_top_of_le_ne_top hM
    (Module.length_le_of_surjective f.hom.rangeRestrict f.hom.surjective_rangeRestrict)

theorem kernel_length_ne_top {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : Module.length R M ≠ ⊤) : Module.length R (LinearMap.ker f.hom) ≠ ⊤ := by
  exact ne_top_of_le_ne_top hM
    (Module.length_le_of_injective (LinearMap.ker f.hom).subtype (Submodule.subtype_injective _))

theorem rationalLength_eq_kernel_add_range {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : Module.length R M ≠ ⊤) :
    rationalLength R M = rationalLength R (.of R (LinearMap.ker f.hom)) +
      rationalLength R (.of R (LinearMap.range f.hom)) := by
  unfold rationalLength
  rw [kernel_range_length R f, ENat.toNat_add
    (kernel_length_ne_top R f hM) (range_length_ne_top R f hM), Nat.cast_add]

theorem rationalLength_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact)
    (hM : Module.length R S.X₂ ≠ ⊤) :
    rationalLength R S.X₂ = rationalLength R (.of R (LinearMap.range S.f.hom)) +
      rationalLength R (.of R (LinearMap.range S.g.hom)) := by
  rw [rationalLength_eq_kernel_add_range R S.g hM]
  have he := LinearMap.exact_iff.mp
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)
  rw [← he]

theorem rationalLength_range_of_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f] :
    rationalLength R (.of R (LinearMap.range f.hom)) = rationalLength R N := by
  unfold rationalLength
  exact congrArg (fun a : ℕ∞ => (a.toNat : ℚ))
    (LinearEquiv.ofTop (LinearMap.range f.hom)
      (LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective f).mp inferInstance))).length_eq

theorem rationalLength_range_of_zero {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : f = 0) : rationalLength R (.of R (LinearMap.range f.hom)) = 0 := by
  subst f
  have hz : Module.length R (LinearMap.range (0 : M →ₗ[R] N)) = 0 := by
    rw [LinearMap.range_zero]
    exact Module.length_eq_zero
  simp only [rationalLength, ModuleCat.hom_zero, hz, ENat.toNat_zero, Nat.cast_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength
