import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.EuclideanCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction

/-! # Diagonal Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DiagonalCoordinates.Construction

noncomputable section

/-! Ordinary real coordinates for bilinear operations and their
diagonal change-of-basis weights. -/

open scoped Classical OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L ι : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
  [Fintype ι]

def continuousBilinearCoordinates (b : Module.Basis ι ℝ L) :
    (L →L[ℝ] L →L[ℝ] L) ≃L[ℝ] (ι × ι × ι → ℝ) :=
  ((ContinuousBracketChange.Construction.finiteBilinearEquiv.symm.trans (EuclideanCoordinates.Construction.bilinearNestedBasisCoordinates b)).trans
    (EuclideanCoordinates.Construction.tripleUncurryLinearEquiv ℝ ι)).toContinuousLinearEquiv

theorem continuousBilinearCoordinates_apply (b : Module.Basis ι ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (i j l : ι) :
    continuousBilinearCoordinates b B (i, j, l) = b.equivFun (B (b i) (b j)) l := rfl

omit [FiniteDimensional ℝ L] in
theorem diagonal_operator_coordinate (b : Module.Basis ι ℝ L)
    (A : L →L[ℝ] L) (a : ι → ℝ) (hA : ∀ i, A (b i) = a i • b i) (x : L) (i : ι) :
    b.equivFun (A x) i = a i * b.equivFun x i := by
  have he : (b.coord i).comp A.toLinearMap = a i • b.coord i := by
    apply b.ext
    intro j
    simp only [Module.Basis.coord_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      hA, map_smul, smul_eq_mul, LinearMap.smul_apply,
      Module.Basis.repr_self_apply]
    by_cases hij : j = i
    · subst j; rfl
    · simp [hij]
  exact LinearMap.congr_fun he x

omit [FiniteDimensional ℝ L] [Fintype ι] in
theorem diagonal_unit_inverse_basis (b : Module.Basis ι ℝ L)
    (g : (L →L[ℝ] L)ˣ) (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ i, g.val (b i) = a i • b i) (i : ι) :
    (g⁻¹).val (b i) = (a i)⁻¹ • b i := by
  apply (ContinuousLinearEquiv.ofUnit g).injective
  change g.val ((g⁻¹).val (b i)) = g.val ((a i)⁻¹ • b i)
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
    Units.mul_inv, one_apply_eq_self, map_smul, hg, smul_smul, inv_mul_cancel₀ (ha i), one_smul]

theorem continuousBilinearCoordinates_diagonal_action (b : Module.Basis ι ℝ L)
    (g : (L →L[ℝ] L)ˣ) (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hg : ∀ i, g.val (b i) = a i • b i) (B : L →L[ℝ] L →L[ℝ] L) (i j l : ι) :
    continuousBilinearCoordinates b (g • B) (i, j, l) =
      (a l * (a i)⁻¹ * (a j)⁻¹) * continuousBilinearCoordinates b B (i, j, l) := by
  change b.equivFun (g.val (B ((g⁻¹).val (b i)) ((g⁻¹).val (b j)))) l = _
  rw [diagonal_unit_inverse_basis b g a ha hg, diagonal_unit_inverse_basis b g a ha hg,
    diagonal_operator_coordinate b g.val a hg]
  simp only [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, continuousBilinearCoordinates_apply]
  ring

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DiagonalCoordinates.Construction
