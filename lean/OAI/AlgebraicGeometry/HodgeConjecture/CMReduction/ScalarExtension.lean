import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Rat

/-! # Scalar Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ScalarExtension.CM.Construction

noncomputable section

/-! Extension of rational cycle-image compatibility to complex coefficients.
These lemmas apply to arbitrary subspaces and the specified comparison maps;
they do not presume any Hodge class belongs to the cycle-class image. -/

open scoped TensorProduct

variable {U V W UC VC WC : Type*}
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]
  [AddCommGroup UC] [Module ℂ UC] [AddCommGroup VC] [Module ℂ VC]
  [AddCommGroup WC] [Module ℂ WC]

theorem linear_preserves_complex_image
    (P : Submodule ℚ U) (Q : Submodule ℚ V)
    (j : ℂ ⊗[ℚ] U →ₗ[ℂ] UC) (k : ℂ ⊗[ℚ] V →ₗ[ℂ] VC)
    (f : U →ₗ[ℚ] V) (F : UC →ₗ[ℂ] VC)
    (hf : ∀ a ∈ P, f a ∈ Q)
    (hF : ∀ a, F (j ((1 : ℂ) ⊗ₜ[ℚ] a)) = k ((1 : ℂ) ⊗ₜ[ℚ] f a))
    (x : UC) (hx : x ∈ (P.baseChange ℂ).map j) :
    F x ∈ (Q.baseChange ℂ).map k := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [Submodule.baseChange_eq_span] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨a, ha, rfl⟩ := ht
      change F (j ((1 : ℂ) ⊗ₜ[ℚ] a)) ∈ (Q.baseChange ℂ).map k
      rw [hF]
      exact ⟨(1 : ℂ) ⊗ₜ[ℚ] f a, Submodule.tmul_mem_baseChange_of_mem 1 (hf a ha), rfl⟩
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
      simpa only [map_add] using ((Q.baseChange ℂ).map k).add_mem hx hy
  | smul c x _ hx =>
      simpa only [map_smul] using ((Q.baseChange ℂ).map k).smul_mem c hx

theorem bilinear_preserves_complex_image
    (P : Submodule ℚ U) (Q : Submodule ℚ V) (S : Submodule ℚ W)
    (j : ℂ ⊗[ℚ] U →ₗ[ℂ] UC) (k : ℂ ⊗[ℚ] V →ₗ[ℂ] VC)
    (l : ℂ ⊗[ℚ] W →ₗ[ℂ] WC)
    (f : U →ₗ[ℚ] V →ₗ[ℚ] W) (F : UC →ₗ[ℂ] VC →ₗ[ℂ] WC)
    (hf : ∀ a ∈ P, ∀ b ∈ Q, f a b ∈ S)
    (hF : ∀ a b, F (j ((1 : ℂ) ⊗ₜ[ℚ] a)) (k ((1 : ℂ) ⊗ₜ[ℚ] b)) =
      l ((1 : ℂ) ⊗ₜ[ℚ] f a b))
    (x : UC) (y : VC)
    (hx : x ∈ (P.baseChange ℂ).map j) (hy : y ∈ (Q.baseChange ℂ).map k) :
    F x y ∈ (S.baseChange ℂ).map l := by
  have hfirst (a : U) (ha : a ∈ P) :
      F (j ((1 : ℂ) ⊗ₜ[ℚ] a)) y ∈ (S.baseChange ℂ).map l :=
    linear_preserves_complex_image Q S k l (f a) (F (j ((1 : ℂ) ⊗ₜ[ℚ] a)))
      (hf a ha) (hF a) y hy
  obtain ⟨t, ht, rfl⟩ := hx
  rw [Submodule.baseChange_eq_span] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨a, ha, rfl⟩ := ht
      exact hfirst a ha
  | zero => simp only [map_zero, LinearMap.zero_apply, Submodule.zero_mem]
  | add x z _ _ hx hz =>
      simpa only [map_add, LinearMap.add_apply] using ((S.baseChange ℂ).map l).add_mem hx hz
  | smul c x _ hx =>
      simpa only [map_smul, LinearMap.smul_apply] using ((S.baseChange ℂ).map l).smul_mem c hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ScalarExtension.CM.Construction
