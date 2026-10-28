import OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant
import OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients
import OAI.RepresentationTheory.Theta.Adelic.IntegralModulus
import OAI.RepresentationTheory.Theta.Adelic.IntegralQuadraticIdeles
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization

/-! # Integral Normalization Scalars -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralNormalizationScalars

noncomputable section

/-! Both actual corrected unitary normalizing scalars equal one for
integral unimodular data at an unramified place. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant OAI.RepresentationTheory.Theta.Adelic.IntegralModulus
open OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients OAI.RepresentationTheory.Theta.Adelic.IntegralQuadraticIdeles

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
variable (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

variable (hdi : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d)⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v)

include hdi in
theorem localDelta_integral_unit : Weil.AdelicSplitting.Normalization.Construction.localDelta F d hd v ∈ IntegralQuadraticIdeles.orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) := by
  constructor
  · apply Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff
    · exact (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem
    · exact (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).one_mem
  · apply Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff
    · exact (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem
    · exact hdi

variable (hdv : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v)
variable (hNorm : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ,
  a.val ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v → a.val⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v → Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a = 1)

include hdv hNorm in
theorem normCharacterScalar_integral_fixed (z : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ)
    (hz : star z = z) (hi : z ∈ IntegralQuadraticIdeles.orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)) :
    Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar F d v z.val.re = 1 := by
  let a := FixedDeterminant.scalarReUnit (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) z hz
  have hr : a.val ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v :=
    ((QuadraticIntegralCoefficients.quadraticOrder_coefficients F d v hdv z.val).mp hi.1).1
  have hinv : a.val⁻¹ = z.inv.re := by
    have h := congrArg (fun u : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ => u.inv.re)
      (FixedDeterminant.scalarUnits_scalarReUnit (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) z hz)
    exact h
  have har : a.val⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v := by
    rw [hinv]
    exact ((QuadraticIntegralCoefficients.quadraticOrder_coefficients F d v hdv z.inv).mp hi.2).1
  unfold Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar
  rw [dite_eq_left (FixedDeterminant.fixedUnit_re_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) z hz)]
  exact hNorm a hr har

variable {n m : ℕ} (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m)
variable (hWeil : Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)
  (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ v) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) = 1)
variable (hχV : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
  a.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v → a.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v → Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV v a = 1)
variable (hχW : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
  a.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v → a.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v → Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW v a = 1)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
variable (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
variable (hHI : ∀ i j, H.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
variable (hHi : ∀ i j, H.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
variable (hKI : ∀ i j, K.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
variable (hKi : ∀ i j, K.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)

include hdi hdv hNorm hWeil hχW hHI hHi hKI hKi hK in
theorem correctedFirstFactorScalar_integral
    (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hui : ∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
    (hui' : ∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) :
    Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v H K u = 1 := by
  let S := IntegralQuadraticIdeles.orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
  have hδ : Weil.AdelicSplitting.Normalization.Construction.localDelta F d hd v ∈ S := localDelta_integral_unit F d hd v hdi
  have hdetH : Matrix.GeneralLinearGroup.det H ∈ S :=
    ⟨IntegralModulus.integral_determinant _ hHI, IntegralModulus.integral_determinant _ hHi⟩
  have hdetK : Matrix.GeneralLinearGroup.det K ∈ S :=
    ⟨IntegralModulus.integral_determinant _ hKI, IntegralModulus.integral_determinant _ hKi⟩
  have hdetU : Matrix.GeneralLinearGroup.det u ∈ S :=
    ⟨IntegralModulus.integral_determinant _ hui, IntegralModulus.integral_determinant _ hui'⟩
  have harg := S.mul_mem (S.mul_mem (S.pow_mem hδ n) hdetH) hdetU
  have hχ := hχW _ harg.1 harg.2
  have hnorm := normCharacterScalar_integral_fixed F d v hdv hNorm
    ((Weil.AdelicSplitting.Normalization.Construction.localDelta F d hd v)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K)
    (FixedDeterminant.skew_det_fixed (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) ((map_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr hd) K hK)
    (S.mul_mem (S.pow_mem (S.inv_mem hδ) m) hdetK)
  simp only [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedFirstFactorScalar, hWeil, inv_one, one_pow, hnorm, hχ,
    Circle.coe_one, mul_one]

include hdv hNorm hWeil hχV hHI hHi hKI hKi hH in
theorem correctedSecondFactorScalar_integral
    (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hui : ∀ i j, u.val i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
    (hui' : ∀ i j, u.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) :
    Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v H K u = 1 := by
  let S := IntegralQuadraticIdeles.orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v)
  have hdetH : Matrix.GeneralLinearGroup.det H ∈ S :=
    ⟨IntegralModulus.integral_determinant _ hHI, IntegralModulus.integral_determinant _ hHi⟩
  have hdetK : Matrix.GeneralLinearGroup.det K ∈ S :=
    ⟨IntegralModulus.integral_determinant _ hKI, IntegralModulus.integral_determinant _ hKi⟩
  have hdetU : Matrix.GeneralLinearGroup.det u ∈ S :=
    ⟨IntegralModulus.integral_determinant _ hui, IntegralModulus.integral_determinant _ hui'⟩
  have harg := S.mul_mem hdetK hdetU
  have hχ := hχV _ harg.1 harg.2
  have hnorm := normCharacterScalar_integral_fixed F d v hdv hNorm
    (Matrix.GeneralLinearGroup.det H) (FixedDeterminant.hermitian_det_fixed (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) H hH) hdetH
  simp only [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedSecondFactorScalar, hWeil, inv_one, one_pow, hnorm, hχ,
    Circle.coe_one, mul_one]

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralNormalizationScalars
