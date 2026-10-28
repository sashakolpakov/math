import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeVectorSpaceContraction

/-! # Cube Kunneth Degree One -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeKunnethDegreeOne.Construction.CubeCech

noncomputable section

/-! The degree-one Kunneth injection for augmented complexes of vector spaces. -/

open scoped TensorProduct

universe u v w v' w'

variable {k : Type u} [Field k]
    {C₀ : Type v} {C₁ : Type v'} {D₀ : Type w} {D₁ : Type w'}
    [AddCommGroup C₀] [Module k C₀] [AddCommGroup C₁] [Module k C₁]
    [AddCommGroup D₀] [Module k D₀] [AddCommGroup D₁] [Module k D₁]
    (uC : k →ₗ[k] C₀) (uD : k →ₗ[k] D₀)
    (eC : C₀ →ₗ[k] k) (eD : D₀ →ₗ[k] k)
    (dC : C₀ →ₗ[k] C₁) (dD : D₀ →ₗ[k] D₁)
    (heC : eC.comp uC = LinearMap.id) (heD : eD.comp uD = LinearMap.id)
    (hexC : Function.Exact uC dC) (hexD : Function.Exact uD dD)

include heC heD hexC hexD in
theorem tensor_degreeOne_boundary_of_zero_restrictions
    (a : C₁ ⊗[k] D₀) (b : C₀ ⊗[k] D₁)
    (hmix : TensorProduct.map LinearMap.id dD a = TensorProduct.map dC LinearMap.id b)
    (ha : TensorProduct.map LinearMap.id eD a = 0)
    (hb : TensorProduct.map eC LinearMap.id b = 0) :
    ∃ t : C₀ ⊗[k] D₀,
      TensorProduct.map dC LinearMap.id t = a ∧ TensorProduct.map LinearMap.id dD t = b := by
  obtain ⟨hC, hc⟩ := CubeVectorSpaceContraction.Construction.CubeCech.augmented_vectorSpace_contraction uC eC dC heC hexC
  obtain ⟨hD, hd⟩ := CubeVectorSpaceContraction.Construction.CubeCech.augmented_vectorSpace_contraction uD eD dD heD hexD
  exact CubeTensorCocycles.Construction.CubeCech.mixed_tensor_cocycle_is_boundary dC dD hC hD uC uD eC eD hc hd
    (CubeVectorSpaceContraction.Construction.CubeCech.augmented_exact_comp_zero uC dC hexC) a b hmix ha hb

include heC heD hexC hexD in
theorem tensor_degreeOne_boundary_of_exact_restrictions
    (a : C₁ ⊗[k] D₀) (b : C₀ ⊗[k] D₁)
    (hmix : TensorProduct.map LinearMap.id dD a = TensorProduct.map dC LinearMap.id b)
    (x : C₀) (y : D₀)
    (ha : TensorProduct.map LinearMap.id eD a = dC x ⊗ₜ[k] (1 : k))
    (hb : TensorProduct.map eC LinearMap.id b = (1 : k) ⊗ₜ[k] dD y) :
    ∃ t : C₀ ⊗[k] D₀,
      TensorProduct.map dC LinearMap.id t = a ∧ TensorProduct.map LinearMap.id dD t = b := by
  have dc : dC (uC 1) = 0 := LinearMap.congr_fun (CubeVectorSpaceContraction.Construction.CubeCech.augmented_exact_comp_zero uC dC hexC) 1
  have dd : dD (uD 1) = 0 := LinearMap.congr_fun (CubeVectorSpaceContraction.Construction.CubeCech.augmented_exact_comp_zero uD dD hexD) 1
  have ec : eC (uC 1) = 1 := LinearMap.congr_fun heC 1
  have ed : eD (uD 1) = 1 := LinearMap.congr_fun heD 1
  let a₀ := a - dC x ⊗ₜ[k] uD 1
  let b₀ := b - uC 1 ⊗ₜ[k] dD y
  have hmix₀ : TensorProduct.map LinearMap.id dD a₀ = TensorProduct.map dC LinearMap.id b₀ := by
    simpa [a₀, b₀, dc, dd] using hmix
  have ha₀ : TensorProduct.map LinearMap.id eD a₀ = 0 := by
    simp [a₀, ha, ed]
  have hb₀ : TensorProduct.map eC LinearMap.id b₀ = 0 := by
    simp [b₀, hb, ec]
  obtain ⟨t, htC, htD⟩ := tensor_degreeOne_boundary_of_zero_restrictions
    uC uD eC eD dC dD heC heD hexC hexD a₀ b₀ hmix₀ ha₀ hb₀
  refine ⟨t + x ⊗ₜ[k] uD 1 + uC 1 ⊗ₜ[k] y, ?_, ?_⟩
  · simp [htC, a₀, dc]
  · simp [htD, b₀, dd]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeKunnethDegreeOne.Construction.CubeCech
