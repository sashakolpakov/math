import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorCoefficients

/-! # Algebra Map Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AlgebraMapDescent

noncomputable section

/-! Maps from finite type algebras into a flat tensor model descend over finite coefficients. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B] [Algebra.FiniteType C A]

theorem finiteType_algHom_coefficient_range (φ : A →ₐ[C] R ⊗[C] B)
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ a, φ a ∈ (Coefficient.TensorMaps.coefficientTensorMap (B := B) D).range := by
  have hfg : (⊤ : Subalgebra C A).FG := Algebra.FiniteType.out
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨D, hED, hD, hx⟩ := Finite.TensorCoefficients.exists_finite_tensor_coefficients (fun a : s => φ a.val) E hE
  have hle : Algebra.adjoin C (s : Set A) ≤
      ((Coefficient.TensorMaps.coefficientTensorMap (B := B) D).range).comap φ :=
    Algebra.adjoin_le (fun a ha => hx ⟨a, ha⟩)
  refine ⟨D, hED, hD, ?_⟩
  intro a
  exact hle (hs.symm ▸ (show a ∈ (⊤ : Subalgebra C A) from trivial))

theorem existsUnique_flat_algHom_coefficient_descent [Module.Flat C B]
    (φ : A →ₐ[C] R ⊗[C] B) (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃! ψ : A →ₐ[C] D ⊗[C] B, (Coefficient.TensorMaps.coefficientTensorMap D).comp ψ = φ := by
  obtain ⟨D, hED, hD, hφ⟩ := finiteType_algHom_coefficient_range φ E hE
  let j := Coefficient.TensorMaps.coefficientTensorMap (B := B) D
  let e := AlgEquiv.ofInjective j (Coefficient.TensorMaps.coefficientTensorMap_injective D)
  let q := φ.codRestrict j.range hφ
  let ψ := e.symm.toAlgHom.comp q
  have hψ : j.comp ψ = φ := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (q a))
  refine ⟨D, hED, hD, ψ, hψ, ?_⟩
  intro χ hχ
  ext a
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  exact (DFunLike.congr_fun hχ a).trans (DFunLike.congr_fun hψ a).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AlgebraMapDescent
