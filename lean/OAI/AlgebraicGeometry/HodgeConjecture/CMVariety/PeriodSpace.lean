import OAI.AlgebraicGeometry.ComplexMultiplication.CM.IntegralPolarization
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Period Space -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodSpace.CM.Abelian

noncomputable section

/-! The real period space of an arbitrary rational weight-one Hodge structure. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

theorem coefficientConjugation_complex_smul (z : ℂ) (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation U (z • x) = star z • ComplexMultiplication.WeightOne.CM.coefficientConjugation U x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a u => simp [TensorProduct.smul_tmul']

theorem coefficientConjugation_real_smul (r : ℝ) (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation U (r • x) = r • ComplexMultiplication.WeightOne.CM.coefficientConjugation U x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a u => simp [TensorProduct.smul_tmul', Complex.real_smul]

/-- The real form inside the actual complexification, defined by conjugation. -/
def realPeriodSpace (U : Type*) [AddCommGroup U] [Module ℚ U] :
    Submodule ℝ (ComplexMultiplication.WeightOne.CM.Complexification U) where
  carrier := {x | ComplexMultiplication.WeightOne.CM.coefficientConjugation U x = x}
  zero_mem' := map_zero _
  add_mem' := by
    intro x y hx hy
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U x = x at hx
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U y = y at hy
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' r x hx := by
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U x = x at hx
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U (r • x) = r • x
    rw [coefficientConjugation_real_smul, hx]

/-- Projection of the real form onto the antiholomorphic summand. -/
def periodProjection (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    realPeriodSpace U →ₗ[ℝ] H.antiholomorphic :=
  ((H.antiholomorphic.projectionOnto H.holomorphic H.complementary.symm).restrictScalars ℝ).comp
    (realPeriodSpace U).subtype

theorem conjugate_antiholomorphic_mem (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (v : H.antiholomorphic) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation U (v : ComplexMultiplication.WeightOne.CM.Complexification U) ∈ H.holomorphic := by
  apply (H.conjugate_mem _).mp
  simpa only [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] using v.property

theorem periodProjection_surjective (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    Function.Surjective (periodProjection H) := by
  intro v
  have hfixed : ComplexMultiplication.WeightOne.CM.coefficientConjugation U
      ((v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v) =
      (v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v := by
    simp only [map_add, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, add_comm]
  refine ⟨⟨(v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v, hfixed⟩, ?_⟩
  change H.antiholomorphic.projectionOnto H.holomorphic H.complementary.symm
    ((v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v) = v
  rw [map_add, Submodule.projectionOnto_apply_left,
    Submodule.projectionOnto_apply_of_mem_right H.complementary.symm
      (conjugate_antiholomorphic_mem H v), add_zero]

theorem periodProjection_injective (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    Function.Injective (periodProjection H) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hzero : periodProjection H x = 0 := hx
  have hhol : (x : ComplexMultiplication.WeightOne.CM.Complexification U) ∈ H.holomorphic :=
    (Submodule.projectionOnto_apply_eq_zero_iff H.complementary.symm).mp hzero
  have hanti : (x : ComplexMultiplication.WeightOne.CM.Complexification U) ∈ H.antiholomorphic := by
    have hc := (H.conjugate_mem x).mpr hhol
    have hfixed : ComplexMultiplication.WeightOne.CM.coefficientConjugation U (x : ComplexMultiplication.WeightOne.CM.Complexification U) = x := x.property
    rw [hfixed] at hc
    exact hc
  have hinter : (x : ComplexMultiplication.WeightOne.CM.Complexification U) ∈ H.holomorphic ⊓ H.antiholomorphic :=
    ⟨hhol, hanti⟩
  have hx0 : (x : ComplexMultiplication.WeightOne.CM.Complexification U) = 0 := by
    simpa only [H.complementary.inf_eq_bot, Submodule.mem_bot] using hinter
  change x = 0
  exact Subtype.ext hx0

/-- The antiholomorphic summand is the real period space with its complex structure. -/
def periodRealEquiv (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    realPeriodSpace U ≃ₗ[ℝ] H.antiholomorphic :=
  LinearEquiv.ofBijective (periodProjection H)
    ⟨periodProjection_injective H, periodProjection_surjective H⟩

theorem periodRealEquiv_symm_coe (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (v : H.antiholomorphic) :
    ((periodRealEquiv H).symm v : ComplexMultiplication.WeightOne.CM.Complexification U) =
      (v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v := by
  have hfixed : ComplexMultiplication.WeightOne.CM.coefficientConjugation U
      ((v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v) =
      (v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v := by
    simp only [map_add, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, add_comm]
  have he : periodRealEquiv H
      ⟨(v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v, hfixed⟩ = v := by
    change H.antiholomorphic.projectionOnto H.holomorphic H.complementary.symm
      ((v : ComplexMultiplication.WeightOne.CM.Complexification U) + ComplexMultiplication.WeightOne.CM.coefficientConjugation U v) = v
    rw [map_add, Submodule.projectionOnto_apply_left,
      Submodule.projectionOnto_apply_of_mem_right H.complementary.symm
        (conjugate_antiholomorphic_mem H v), add_zero]
  exact congrArg Subtype.val ((periodRealEquiv H).symm_apply_eq.mpr he.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodSpace.CM.Abelian
