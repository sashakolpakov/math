import OAI.RepresentationTheory.Theta.Geometric.CharacteristicDeterminantCongruence
import OAI.RepresentationTheory.Theta.Geometric.LatticeIntegralOperator

/-! # Lattice Determinant Congruence -/

namespace OAI.RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence

noncomputable section

/-! A principal congruence on a full integral lattice gives determinant
congruence at the same level, without clearing basis denominators. -/

theorem integral_operator_determinant_congruence {E I : Type*} [Field E] [CharZero E]
    [Fintype I] [DecidableEq I] (f : Module.End E (I → E)) (hf : IsIntegral ℤ f) (N : ℕ) :
    ∃ a : E, IsIntegral ℤ a ∧ LinearMap.det (1 + (N : E) • f) = 1 + (N : E) * a := by
  let M := LinearMap.toMatrix' f
  have hc (n) : IsIntegral ℤ (M.charpoly.coeff n) := by
    rw [← Matrix.charpoly_toLin', Matrix.toLin'_toMatrix']
    exact IntegralCharacteristicCoefficients.integral_characteristic_coefficient f hf n
  obtain ⟨a, ha, he⟩ := CharacteristicDeterminantCongruence.characteristic_determinant_congruence M hc N
  refine ⟨a, ha, ?_⟩
  rw [← LinearMap.det_toMatrix']
  rw [map_add, map_smul, LinearMap.toMatrix'_one]
  exact he

theorem lattice_determinant_congruence {E I J : Type*} [Field E] [CharZero E] [Algebra ℚ E]
    [Fintype I] [DecidableEq I] [Fintype J]
    (L : Submodule ℤ (I → E)) (b : Module.Basis J ℤ L)
    (hspan : Submodule.span ℚ (L : Set (I → E)) = ⊤)
    (g : (I → E) ≃ₗ[E] (I → E)) (N : ℕ) (hN : N ≠ 0)
    (hg : ∀ x ∈ L, ∃ y ∈ L, g x - x = N • y) :
    ∃ a : E, IsIntegral ℤ a ∧ LinearMap.det g.toLinearMap = 1 + (N : E) * a := by
  let f : Module.End E (I → E) := (N : E)⁻¹ • (g.toLinearMap - 1)
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hf (x) (hx : x ∈ L) : f x ∈ L := by
    obtain ⟨y, hy, he⟩ := hg x hx
    change (N : E)⁻¹ • (g x - x) ∈ L
    rw [he, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
    exact hy
  have hint : IsIntegral ℤ f := LatticeIntegralOperator.lattice_operator_isIntegral L b hspan f hf
  have he : 1 + (N : E) • f = g.toLinearMap := by
    dsimp only [f]
    rw [smul_smul, mul_inv_cancel₀ hNE, one_smul, add_sub_cancel]
  obtain ⟨a, ha, hdet⟩ := integral_operator_determinant_congruence f hint N
  exact ⟨a, ha, he ▸ hdet⟩

end

end OAI.RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence
