import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisActionRelations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflexiveTransposeAction
import Mathlib.RingTheory.LocalProperties.Basic

/-! # Basis Local Dual Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisLocalDualRelations

noncomputable section

/-! The integral multiplication relations for operators on a reflexive
module can be proved from their actual actions on all local coefficient
duals. Localization detects equality over the original ring. -/

open _root_.Module

variable {O R V I : Type} [CommRing O] [CommRing R] [AddCommGroup V] [Module R V]
  (b : Basis I ℤ O) (d : I → Module.End R V)

theorem integralBasis_localDual_extension {C : Type} [CommRing C] [Algebra R C]
    (ρ : O →+* Module.End C (V →ₗ[R] C))
    (hρ : ∀ i (ℓ : V →ₗ[R] C) v, ℓ (d i v) = (ρ (b i) ℓ) v)
    (x : O) (ℓ : V →ₗ[R] C) (v : V) :
    ℓ (b.constr ℤ d x v) = (ρ x ℓ) v := by
  let L : O →ₗ[ℤ] C :=
    { toFun := fun x => ℓ (b.constr ℤ d x v)
      map_add' x y := by simp only [map_add, LinearMap.add_apply]
      map_smul' n x := by simp only [map_smul, LinearMap.smul_apply, map_zsmul, RingHom.id_apply] }
  let M : O →ₗ[ℤ] C :=
    { toFun := fun x => (ρ x ℓ) v
      map_add' x y := by simp only [map_add, LinearMap.add_apply]
      map_smul' n x := by simp only [map_zsmul, LinearMap.smul_apply, RingHom.id_apply] }
  have h : L = M := b.ext (fun i => by
    change ℓ (b.constr ℤ d (b i) v) = (ρ (b i) ℓ) v
    rw [Basis.constr_basis]
    exact hρ i ℓ v)
  exact LinearMap.congr_fun h x

theorem localDuals_detect_eq [Module.IsReflexive R V] (x y : V)
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal) (ℓ : V →ₗ[R] Localization.AtPrime P), ℓ x = ℓ y) :
    x = y := by
  apply ReflexiveTransposeAction.reflexive_eq_of_dual (R := R)
  intro ℓ
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro P hP
  let φ : V →ₗ[R] Localization.AtPrime P := (Algebra.linearMap R (Localization.AtPrime P)).comp ℓ
  have hh : algebraMap R (Localization.AtPrime P) (ℓ x) =
      algebraMap R (Localization.AtPrime P) (ℓ y) := h P hP φ
  exact (map_sub (algebraMap R (Localization.AtPrime P)) (ℓ x) (ℓ y)).trans (sub_eq_zero.mpr hh)

theorem integralBasisActionRelations_of_localDualActions [Module.IsReflexive R V]
    (hρ : ∀ (P : Ideal R) (_ : P.IsMaximal),
      ∃ ρ : O →+* Module.End (Localization.AtPrime P) (V →ₗ[R] Localization.AtPrime P),
        ∀ i (ℓ : V →ₗ[R] Localization.AtPrime P) v, ℓ (d i v) = (ρ (b i) ℓ) v) :
    BasisActionRelations.IntegralBasisActionRelations b d := by
  constructor
  · apply LinearMap.ext
    intro v
    apply localDuals_detect_eq (R := R)
    intro P hP ℓ
    obtain ⟨ρ, hρ⟩ := hρ P hP
    rw [integralBasis_localDual_extension b d ρ hρ, map_one]
    rfl
  · intro i j
    apply LinearMap.ext
    intro v
    apply localDuals_detect_eq (R := R)
    intro P hP ℓ
    obtain ⟨ρ, hρ⟩ := hρ P hP
    change ℓ (b.constr ℤ d (b i * b j) v) = ℓ (d i (d j v))
    rw [integralBasis_localDual_extension b d ρ hρ, hρ, hρ]
    rw [mul_comm (b i) (b j), map_mul]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisLocalDualRelations
