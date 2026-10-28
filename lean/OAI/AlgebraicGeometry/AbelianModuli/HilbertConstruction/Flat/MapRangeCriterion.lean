import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorScalarCompatibility

/-! # Map Range Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MapRangeCriterion

noncomputable section

/-! A flat model admits unique map descent whenever the images lie in its coefficient range. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B] [Module.Flat C B]

theorem existsUnique_flat_algHom_descent_of_range (D : Subalgebra C R)
    (φ : A →ₐ[C] R ⊗[C] B) (hφ : ∀ a, φ a ∈ (Coefficient.TensorMaps.coefficientTensorMap D).range) :
    ∃! ψ : A →ₐ[C] D ⊗[C] B, (Coefficient.TensorMaps.coefficientTensorMap D).comp ψ = φ := by
  let j := Coefficient.TensorMaps.coefficientTensorMap (B := B) D
  let e := AlgEquiv.ofInjective j (Coefficient.TensorMaps.coefficientTensorMap_injective D)
  let q := φ.codRestrict j.range hφ
  let ψ := e.symm.toAlgHom.comp q
  have hψ : j.comp ψ = φ := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (q a))
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  ext a
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  exact (DFunLike.congr_fun hχ a).trans (DFunLike.congr_fun hψ a).symm

theorem existsUnique_flat_tensorHom_descent_of_range (D : Subalgebra C R)
    (φ : R ⊗[C] A →ₐ[R] R ⊗[C] B)
    (hφ : ∀ a, φ (1 ⊗ₜ[C] a) ∈ (Coefficient.TensorMaps.coefficientTensorMap D).range) :
    ∃! ψ : D ⊗[C] A →ₐ[D] D ⊗[C] B,
      ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ (Coefficient.TensorMaps.coefficientTensorMap D x) := by
  obtain ⟨ψ₀, hψ₀, _⟩ := existsUnique_flat_algHom_descent_of_range D
    ((AlgHom.liftEquiv C R A (R ⊗[C] B)).symm φ) hφ
  let ψ := (AlgHom.liftEquiv C D A (D ⊗[C] B)) ψ₀
  have hψ : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ (Coefficient.TensorMaps.coefficientTensorMap D x) :=
    Coefficient.TensorScalarCompatibility.coefficientTensorMap_liftEquiv D φ ψ₀ hψ₀
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  apply AlgHom.ext
  intro x
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  exact (hχ x).trans (hψ x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MapRangeCriterion
