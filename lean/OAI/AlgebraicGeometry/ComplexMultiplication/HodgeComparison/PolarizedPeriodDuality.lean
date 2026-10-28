import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Polarized Period Duality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizedPeriodDuality.CM.Construction

noncomputable section

/-! A polarization identifies the antiholomorphic period space with
the complex dual of the holomorphic space. Dual rational bases retain
the exact period-coordinate values. -/

open scoped TensorProduct

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  {H : WeightOne.CM.WeightOneHodgeStructure U} (P : CM.Polarization.WeightOnePolarization H)

def polarizedHolomorphicDual : H.antiholomorphic →ₗ[ℂ] Module.Dual ℂ H.holomorphic :=
  (P.form.baseChange ℂ).flip.compl₁₂ H.antiholomorphic.subtype H.holomorphic.subtype

def polarizedAntiholomorphicDual : H.holomorphic →ₗ[ℂ] Module.Dual ℂ H.antiholomorphic :=
  (P.form.baseChange ℂ).compl₁₂ H.holomorphic.subtype H.antiholomorphic.subtype

theorem polarizedHolomorphicDual_injective : Function.Injective (polarizedHolomorphicDual P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hc : WeightOne.CM.coefficientConjugation U (v : WeightOne.CM.Complexification U) ∈ H.holomorphic :=
    (H.conjugate_mem (WeightOne.CM.coefficientConjugation U v)).mp (by
      rw [WeightOne.CM.coefficientConjugation_involutive]
      exact v.property)
  have he := congrArg (fun f : Module.Dual ℂ H.holomorphic => f ⟨_, hc⟩) hv
  change P.form.baseChange ℂ (WeightOne.CM.coefficientConjugation U v) v = 0 at he
  by_contra hne
  have hcn : WeightOne.CM.coefficientConjugation U (v : WeightOne.CM.Complexification U) ≠ 0 := by
    intro hz
    apply hne
    apply Subtype.ext
    change (v : WeightOne.CM.Complexification U) = 0
    have h := congrArg (WeightOne.CM.coefficientConjugation U) hz
    simpa only [WeightOne.CM.coefficientConjugation_involutive, map_zero] using h
  have hp := P.hodge_positive _ hc hcn
  rw [WeightOne.CM.coefficientConjugation_involutive, he, mul_zero, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem polarizedAntiholomorphicDual_injective : Function.Injective (polarizedAntiholomorphicDual P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have hc : WeightOne.CM.coefficientConjugation U (u : WeightOne.CM.Complexification U) ∈ H.antiholomorphic :=
    (H.conjugate_mem _).mpr u.property
  have he := congrArg (fun f : Module.Dual ℂ H.antiholomorphic => f ⟨_, hc⟩) hu
  change P.form.baseChange ℂ u (WeightOne.CM.coefficientConjugation U u) = 0 at he
  by_contra hne
  have hun : (u : WeightOne.CM.Complexification U) ≠ 0 := fun hz => hne (Subtype.ext hz)
  have hp := P.hodge_positive _ u.property hun
  rw [he, mul_zero, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

include P in
theorem polarizedHolomorphicDual_finrank :
    Module.finrank ℂ H.antiholomorphic = Module.finrank ℂ (Module.Dual ℂ H.holomorphic) := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  have h₁ := LinearMap.finrank_le_finrank_of_injective (polarizedHolomorphicDual_injective P)
  have h₂ := LinearMap.finrank_le_finrank_of_injective (polarizedAntiholomorphicDual_injective P)
  rw [Subspace.dual_finrank_eq] at h₁ h₂ ⊢
  exact le_antisymm h₁ h₂

def polarizedHolomorphicDualEquiv : H.antiholomorphic ≃ₗ[ℂ] Module.Dual ℂ H.holomorphic := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  exact LinearEquiv.ofBijective (polarizedHolomorphicDual P)
    ⟨polarizedHolomorphicDual_injective P,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (polarizedHolomorphicDual_finrank P)).mp
        (polarizedHolomorphicDual_injective P)⟩

theorem polarizedHolomorphicDualEquiv_realVector (v : H.antiholomorphic) (u : H.holomorphic) :
    polarizedHolomorphicDualEquiv P v u =
      P.form.baseChange ℂ u ((v : WeightOne.CM.Complexification U) + WeightOne.CM.coefficientConjugation U v) := by
  have hc : WeightOne.CM.coefficientConjugation U (v : WeightOne.CM.Complexification U) ∈ H.holomorphic :=
    (H.conjugate_mem (WeightOne.CM.coefficientConjugation U v)).mp (by
      rw [WeightOne.CM.coefficientConjugation_involutive]
      exact v.property)
  rw [map_add, P.holomorphic_isotropic u u.property (WeightOne.CM.coefficientConjugation U v) hc, add_zero]
  rfl

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ U)

def polarizationDualRationalBasis : Module.Basis ι ℚ U := by
  classical
  exact P.form.flip.dualBasis P.nondegenerate.flip b

theorem polarizationDualRationalBasis_pair (i : ι) (x : U) :
    P.form x (polarizationDualRationalBasis P b i) = b.repr x i := by
  classical
  have h : P.form.flip (polarizationDualRationalBasis P b i) = b.coord i := by
    apply b.ext
    intro j
    have he := P.form.flip.apply_dualBasis_left P.nondegenerate.flip b i j
    simpa only [polarizationDualRationalBasis, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply] using he
  exact congrArg (fun f : U →ₗ[ℚ] ℚ => f x) h

theorem polarizationDualRationalBasis_complex_pair (i : ι) (u : WeightOne.CM.Complexification U) :
    P.form.baseChange ℂ u ((1 : ℂ) ⊗ₜ[ℚ] polarizationDualRationalBasis P b i) =
      (b.baseChange ℂ).repr u i := by
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
      rw [LinearMap.BilinForm.baseChange_tmul, mul_one,
        polarizationDualRationalBasis_pair, Module.Basis.baseChange_repr_tmul]
  | add u v hu hv => simp [hu, hv]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizedPeriodDuality.CM.Construction
