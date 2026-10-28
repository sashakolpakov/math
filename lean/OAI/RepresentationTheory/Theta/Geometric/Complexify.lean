import Mathlib

/-! # Complexify -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complexify

noncomputable section

section

/-!
# Complex coefficients in GeometricTheta

TateComparison constructs the rational spherical algebra. These constructors retain
GeometricTheta's complex-coefficient conclusion by genuine scalar extension. The
covariance bridge uses the proved complex linearity of the canonical theta
map, so passing to rational coefficients in the local model loses nothing.
-/

open scoped TensorProduct

def complexifyHeckeEquiv
    {A B : Type*} [Semiring A] [Algebra ℚ A] [Semiring B] [Algebra ℚ B]
    (e : A ≃ₐ[ℚ] B) : ℂ ⊗[ℚ] A ≃ₐ[ℂ] ℂ ⊗[ℚ] B :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) e

@[simp] theorem complexifyHeckeEquiv_tmul
    {A B : Type*} [Semiring A] [Algebra ℚ A] [Semiring B] [Algebra ℚ B]
    (e : A ≃ₐ[ℚ] B) (c : ℂ) (a : A) :
    complexifyHeckeEquiv e (c ⊗ₜ[ℚ] a) = c ⊗ₜ[ℚ] e a := rfl

def complexifyOperator
    {A V : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (rho : A →ₗ[ℚ] Module.End ℂ V) :
    ℂ ⊗[ℚ] A →ₗ[ℂ] Module.End ℂ V := rho.liftBaseChange ℂ

/-- Covariance for all complex Hecke elements follows by tensor induction. -/
theorem covariance_extends_to_complex
    {A S V : Type*} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
    [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (theta : S →ₗ[ℂ] V)
    (rho : A →ₗ[ℚ] Module.End ℂ S)
    (tau : A →ₗ[ℚ] Module.End ℂ V)
    (h : ∀ a φ, tau a (theta φ) = theta (rho a φ))
    (a : ℂ ⊗[ℚ] A) (φ : S) :
    complexifyOperator tau a (theta φ) = theta (complexifyOperator rho a φ) := by
  induction a using TensorProduct.inductionOn with
  | tmul c a => simp [complexifyOperator, h]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

end

/-! Operator commutation extends from a spanning family and through the
actual tensor-product complexification of rational Betti operators. -/
open scoped TensorProduct

theorem covariance_of_span {A S V I : Type*}
    [AddCommGroup A] [Module ℚ A]
    [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
    [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (θ : S →ₗ[ℂ] V) (ρ : A →ₗ[ℚ] Module.End ℂ S) (τ : A →ₗ[ℚ] Module.End ℂ V)
    (b : I → A) (hb : Submodule.span ℚ (Set.range b) = ⊤)
    (h : ∀ i φ, τ (b i) (θ φ) = θ (ρ (b i) φ)) (a : A) (φ : S) :
    τ a (θ φ) = θ (ρ a φ) := by
  have ha : a ∈ Submodule.span ℚ (Set.range b) := by rw [hb]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨i, rfl⟩ := ha; exact h i φ
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy hxc hyc => simp only [map_add, LinearMap.add_apply, hxc, hyc]
  | smul c x hx hxc => simp only [map_smul, LinearMap.smul_apply, map_rat_smul, hxc]

theorem linear_commutes_of_span {k K A V I : Type*} [Field k] [Field K] [Algebra k K]
    [AddCommGroup A] [Module k A] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V]
    (ρ : A →ₗ[k] Module.End K V) (p : Module.End K V) (b : I → A)
    (hb : Submodule.span k (Set.range b) = ⊤)
    (h : ∀ i, (ρ (b i)).comp p = p.comp (ρ (b i))) (a : A) :
    (ρ a).comp p = p.comp (ρ a) := by
  have ha : a ∈ Submodule.span k (Set.range b) := by rw [hb]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨i, rfl⟩ := ha; exact h i
  | zero => simp only [map_zero, LinearMap.zero_comp, LinearMap.comp_zero]
  | add x y hx hy hxc hyc => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hxc, hyc]
  | smul c x hx hxc => simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, hxc]

theorem complexified_baseChange_commutes {A V : Type*}
    [AddCommGroup A] [Module ℚ A] [AddCommGroup V] [Module ℚ V]
    (ρ : A →ₗ[ℚ] Module.End ℚ V) (p : Module.End ℚ V)
    (h : ∀ a, (ρ a).comp p = p.comp (ρ a)) (z : ℂ ⊗[ℚ] A) :
    (complexifyOperator ((LinearMap.baseChangeHom (R := ℚ) (M := V) (N := V) ℂ).comp ρ) z).comp
      (p.baseChange ℂ) =
    (p.baseChange ℂ).comp
      (complexifyOperator ((LinearMap.baseChangeHom (R := ℚ) (M := V) (N := V) ℂ).comp ρ) z) := by
  have H (a : A) : ((ρ a).baseChange ℂ).comp (p.baseChange ℂ) =
      (p.baseChange ℂ).comp ((ρ a).baseChange ℂ) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]
  induction z using TensorProduct.inductionOn with
  | tmul c a =>
    change (c • (ρ a).baseChange ℂ).comp (p.baseChange ℂ) =
      (p.baseChange ℂ).comp (c • (ρ a).baseChange ℂ)
    rw [LinearMap.smul_comp, LinearMap.comp_smul, H]
  | add z w hz hw => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hz, hw]

end

end OAI.RepresentationTheory.Theta.Geometric.Complexify
