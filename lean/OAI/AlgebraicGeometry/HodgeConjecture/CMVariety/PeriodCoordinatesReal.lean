import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodSpace
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Period Coordinates Real -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodCoordinatesReal.CM.Abelian

noncomputable section

/-! Real coordinates coming from a rational basis, without a CM-field action. -/

open scoped TensorProduct

variable {U ι : Type*} [AddCommGroup U] [Module ℚ U]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ U)

omit [Fintype ι] [DecidableEq ι] in
theorem complexBasis_repr_conjugate (x : ComplexMultiplication.WeightOne.CM.Complexification U) (i : ι) :
    (b.baseChange ℂ).repr (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x) i =
      star ((b.baseChange ℂ).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, star_add]
  | tmul a u => simp

omit [Fintype ι] [DecidableEq ι] in
theorem complexBasis_repr_real (x : PeriodSpace.CM.Abelian.realPeriodSpace U) (i : ι) :
    (((b.baseChange ℂ).repr (x : ComplexMultiplication.WeightOne.CM.Complexification U) i).re : ℂ) =
      (b.baseChange ℂ).repr (x : ComplexMultiplication.WeightOne.CM.Complexification U) i := by
  apply Complex.conj_eq_iff_re.mp
  have hc := complexBasis_repr_conjugate b (x : ComplexMultiplication.WeightOne.CM.Complexification U) i
  have hfixed : ComplexMultiplication.WeightOne.CM.coefficientConjugation U (x : ComplexMultiplication.WeightOne.CM.Complexification U) = x := x.property
  rw [hfixed] at hc
  exact hc.symm

def realCoordinates : PeriodSpace.CM.Abelian.realPeriodSpace U →ₗ[ℝ] (ι → ℝ) where
  toFun x i := ((b.baseChange ℂ).repr (x : ComplexMultiplication.WeightOne.CM.Complexification U) i).re
  map_add' := by intro x y; ext i; simp
  map_smul' := by
    intro r x
    ext i
    change ((((b.baseChange ℂ).repr.restrictScalars ℝ)
      (r • (x : ComplexMultiplication.WeightOne.CM.Complexification U))) i).re = _
    rw [map_smul]
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem realCoordinates_injective : Function.Injective (realCoordinates b) := by
  intro x y hxy
  apply Subtype.ext
  apply (b.baseChange ℂ).repr.injective
  ext i
  rw [← complexBasis_repr_real b x i, ← complexBasis_repr_real b y i]
  exact congrArg (fun f : ι → ℝ => (f i : ℂ)) hxy

def realCoordinateVector (x : ι → ℝ) : PeriodSpace.CM.Abelian.realPeriodSpace U :=
  ⟨∑ i, x i • (b.baseChange ℂ) i, by
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U (∑ i, x i • (b.baseChange ℂ) i) = _
    simp only [map_sum, PeriodSpace.CM.Abelian.coefficientConjugation_real_smul,
      Module.Basis.baseChange_apply, ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, star_one]⟩

omit [DecidableEq ι] in
theorem realCoordinates_coordinateVector (x : ι → ℝ) :
    realCoordinates b (realCoordinateVector b x) = x := by
  ext i
  simp [realCoordinates, realCoordinateVector, TensorProduct.smul_tmul', Complex.real_smul]

def realCoordinateEquiv : PeriodSpace.CM.Abelian.realPeriodSpace U ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofBijective (realCoordinates b)
    ⟨realCoordinates_injective b,
      fun x => ⟨realCoordinateVector b x, realCoordinates_coordinateVector b x⟩⟩

/-- A rational basis induces an actual real basis of the antiholomorphic period space. -/
def periodRealBasis (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    Module.Basis ι ℝ H.antiholomorphic :=
  (Pi.basisFun ℝ ι).map ((realCoordinateEquiv b).symm.trans (PeriodSpace.CM.Abelian.periodRealEquiv H))

theorem realCoordinateEquiv_symm_basis (i : ι) :
    (((realCoordinateEquiv b).symm ((Pi.basisFun ℝ ι) i)) : ComplexMultiplication.WeightOne.CM.Complexification U) =
      (1 : ℂ) ⊗ₜ[ℚ] b i := by
  let x : PeriodSpace.CM.Abelian.realPeriodSpace U := ⟨(1 : ℂ) ⊗ₜ[ℚ] b i, by
    change ComplexMultiplication.WeightOne.CM.coefficientConjugation U ((1 : ℂ) ⊗ₜ[ℚ] b i) = _
    simp⟩
  have hx : realCoordinateEquiv b x = (Pi.basisFun ℝ ι) i := by
    ext j
    simp [realCoordinateEquiv, realCoordinates, x, Pi.basisFun_apply,
      Finsupp.single_apply, Pi.single_apply, apply_ite, eq_comm]
  exact congrArg Subtype.val ((realCoordinateEquiv b).symm_apply_eq.mpr hx.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodCoordinatesReal.CM.Abelian
