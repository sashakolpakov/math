import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialMatrixCurves
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialCurveGroupPoints
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteIndex

/-! # Unipotent One Parameter -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.UnipotentOneParameter

noncomputable section

/-! Every unipotent point of a characteristic-zero algebraic matrix
group lies on an additive one-parameter subgroup of the same point group. -/

open scoped Classical

variable {F K : Type} [Field F] [Field K] [CharZero K] {n : ℕ}

theorem unipotent_point_has_additive_parameter (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ρ : F →+* K)
    (g : G.Points ρ) (hg : IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G ρ g - 1)) :
    ∃ u : Multiplicative K →* G.Points ρ, u (Multiplicative.ofAdd 1) = g := by
  obtain ⟨P, hP⟩ := PolynomialMatrixCurves.unipotent_has_polynomial_powers (PolynomialGaloisNorm.matrixPointsHom G ρ g) hg
  have hNat (m : ℕ) : ∃ g₀ : G.Points ρ, PolynomialGaloisNorm.matrixPointsHom G ρ g₀ = PolynomialMatrixCurves.evalPolynomialMatrix P (m : K) := by
    refine ⟨g ^ m, ?_⟩
    rw [map_pow, hP]
  choose q hq using PolynomialCurveGroupPoints.polynomial_curve_mem_group_of_nat G ρ P hNat
  let u : Multiplicative K →* G.Points ρ := {
    toFun a := q a.toAdd
    map_one' := by
      apply PolynomialGaloisNorm.matrixPointsHom_injective G ρ
      change PolynomialGaloisNorm.matrixPointsHom G ρ (q 0) = PolynomialGaloisNorm.matrixPointsHom G ρ 1
      rw [map_one, hq]
      simpa only [Nat.cast_zero, pow_zero] using hP 0
    map_mul' a b := by
      apply PolynomialGaloisNorm.matrixPointsHom_injective G ρ
      change PolynomialGaloisNorm.matrixPointsHom G ρ (q (a.toAdd + b.toAdd)) = PolynomialGaloisNorm.matrixPointsHom G ρ (q a.toAdd * q b.toAdd)
      rw [map_mul, hq, hq, hq]
      exact PolynomialMatrixCurves.polynomialMatrix_add_law_of_nat_powers P (PolynomialGaloisNorm.matrixPointsHom G ρ g) hP a.toAdd b.toAdd }
  refine ⟨u, ?_⟩
  apply PolynomialGaloisNorm.matrixPointsHom_injective G ρ
  change PolynomialGaloisNorm.matrixPointsHom G ρ (q 1) = PolynomialGaloisNorm.matrixPointsHom G ρ g
  rw [hq]
  simpa only [Nat.cast_one, pow_one] using hP 1

theorem unipotent_point_mem_additiveParameterElements (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ρ : F →+* K)
    (g : G.Points ρ) (hg : IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G ρ g - 1)) :
    g ∈ FiniteIndex.additiveParameterElements (K := K) (G := G.Points ρ) := by
  obtain ⟨u, hu⟩ := unipotent_point_has_additive_parameter G ρ g hg
  exact ⟨u, 1, hu⟩

theorem additive_generation_of_unipotent_generation (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ρ : F →+* K)
    (hgen : Subgroup.closure {g : G.Points ρ | IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G ρ g - 1)} = ⊤) :
    Subgroup.closure (FiniteIndex.additiveParameterElements (K := K) (G := G.Points ρ)) = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Subgroup.closure_mono (fun g hg => unipotent_point_mem_additiveParameterElements G ρ g hg)

end

end OAI.NumberTheory.Quaternion.Arithmetic.UnipotentOneParameter
