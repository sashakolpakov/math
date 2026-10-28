import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Cokernel Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CokernelLength

/-!
# ProjectionFormula: invariance of divisor length under finite-colength enlargement

An injective endomorphism has the same cokernel length on an invariant
submodule of finite colength. Comparing the two factorizations of the same
composite proves this without assuming a divisor or pushforward identity.
This is the module calculation used for finite birational normalization.
-/

open LinearMap _root_.Submodule

variable {R A B C : Type*} [Ring R]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

theorem length_cokernel_comp (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Injective g) :
    Module.length R (C ⧸ (g.comp f).range) =
      Module.length R (B ⧸ f.range) + Module.length R (C ⧸ g.range) := by
  let u : (B ⧸ f.range) →ₗ[R] C ⧸ (g.comp f).range :=
    f.range.mapQ (g.comp f).range g (by
      rintro y ⟨x, rfl⟩
      exact ⟨x, rfl⟩)
  have hle : (g.comp f).range ≤ g.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  let v : (C ⧸ (g.comp f).range) →ₗ[R] C ⧸ g.range :=
    (g.comp f).range.mapQ g.range LinearMap.id hle
  have hu : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot]
    change (f.range.mapQ (g.comp f).range g _).ker = ⊥
    rw [Submodule.ker_mapQ, LinearMap.range_comp, Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr hg, sup_bot_eq, Submodule.mkQ_map_self]
  have hv : Function.Surjective v := by
    intro c
    obtain ⟨x, rfl⟩ := g.range.mkQ_surjective c
    exact ⟨(g.comp f).range.mkQ x, rfl⟩
  have he : Function.Exact u v := by
    rw [LinearMap.exact_iff]
    change ((g.comp f).range.mapQ g.range LinearMap.id _).ker =
      (f.range.mapQ (g.comp f).range g _).range
    rw [Submodule.range_mapQ, Submodule.ker_mapQ, Submodule.comap_id]
  exact Module.length_eq_add_of_exact u v hu hv he

/-- Finite-colength enlargement does not change the cokernel length of a
compatible injective endomorphism. No length finiteness is required of the
endomorphism's own cokernel. -/
theorem length_cokernel_eq_of_finite_colength
    (i : A →ₗ[R] B) (u : A →ₗ[R] A) (v : B →ₗ[R] B)
    (hi : Function.Injective i) (hv : Function.Injective v)
    (hcomm : i.comp u = v.comp i)
    (hfinite : Module.length R (B ⧸ i.range) ≠ ⊤) :
    Module.length R (A ⧸ u.range) = Module.length R (B ⧸ v.range) := by
  have h₁ := length_cokernel_comp u i hi
  have h₂ := length_cokernel_comp i v hv
  rw [hcomm, h₂] at h₁
  have h₃ : Module.length R (A ⧸ u.range) + Module.length R (B ⧸ i.range) =
      Module.length R (B ⧸ v.range) + Module.length R (B ⧸ i.range) := by
    simpa only [add_comm] using h₁.symm
  exact ENat.add_left_injective_of_ne_top hfinite h₃

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CokernelLength
