import OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization
import Mathlib.RingTheory.Localization.Integer

/-! # Integral Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntegralLattice.CM.Abelian

noncomputable section

/-! Clearing a general rational polarization on the integer span of a rational basis. -/

variable {U ι : Type*} [AddCommGroup U] [Module ℚ U]

theorem integer_bilin_on_span {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V) (s : Set V)
    (hB : ∀ x ∈ s, ∀ y ∈ s, IsLocalization.IsInteger ℤ (B x y)) :
    ∀ x ∈ Submodule.span ℤ s, ∀ y ∈ Submodule.span ℤ s,
      IsLocalization.IsInteger ℤ (B x y) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hB x hx y hy
    | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := K))
    | add y z _ _ hy hz =>
      simpa only [map_add] using IsLocalization.isInteger_add hy hz
    | smul n y _ hy =>
      simpa only [map_zsmul] using (IsLocalization.isInteger_smul (a := n) hy)
  | zero =>
    intro y _
    simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := K))
  | add x z _ _ hx hz =>
    intro y hy
    simpa only [map_add, LinearMap.add_apply] using
      IsLocalization.isInteger_add (hx y hy) (hz y hy)
  | smul n x _ hx =>
    intro y hy
    simpa only [map_zsmul, LinearMap.smul_apply] using
      (IsLocalization.isInteger_smul (a := n) (hx y hy))

theorem exists_positive_integral_basis_scale [Finite ι]
    (B : LinearMap.BilinForm ℚ U) (b : Module.Basis ι ℚ U) :
    ∃ q : ℚ, 0 < q ∧
      ∀ x ∈ Submodule.span ℤ (Set.range b),
        ∀ y ∈ Submodule.span ℤ (Set.range b),
          IsLocalization.IsInteger ℤ ((q • B) x y) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun ij : ι × ι => B (b ij.1) (b ij.2))
  have hd0 : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  let q : ℚ := ((d : ℤ) : ℚ) ^ 2
  refine ⟨q, sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hd0), ?_⟩
  apply integer_bilin_on_span
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  have hi := IsLocalization.isInteger_smul (a := (d : ℤ)) (hd (i, j))
  change IsLocalization.IsInteger ℤ
    (((d : ℤ) : ℚ) * (((d : ℤ) : ℚ) * B (b i) (b j))) at hi
  change IsLocalization.IsInteger ℤ (q * B (b i) (b j))
  simpa only [q, pow_two, mul_assoc] using hi

/-- Every rational polarization becomes integral on the chosen full rational lattice. -/
theorem exists_integral_polarization [Finite ι]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
    (b : Module.Basis ι ℚ U) :
    ∃ P' : ComplexMultiplication.CM.Polarization.WeightOnePolarization H,
      ∀ x ∈ Submodule.span ℤ (Set.range b),
        ∀ y ∈ Submodule.span ℤ (Set.range b),
          IsLocalization.IsInteger ℤ (P'.form x y) := by
  obtain ⟨q, hq, hint⟩ := exists_positive_integral_basis_scale P.form b
  exact ⟨P.positiveScale q hq, hint⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntegralLattice.CM.Abelian
