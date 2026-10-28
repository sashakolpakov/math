import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Integral Characteristic Coefficients -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntegralCharacteristicCoefficients

noncomputable section

/-! An integral linear operator has integral characteristic coefficients.
The proof first uses eigenvectors over an algebraic closure and then
reflects integrality along the scalar-extension embedding. -/

open _root_.Polynomial

theorem integral_eigenvalue {F V : Type*} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] (f : Module.End F V) (hf : IsIntegral ℤ f)
    (a : F) (ha : f.HasEigenvalue a) : IsIntegral ℤ a := by
  obtain ⟨p, hp, hpf⟩ := hf
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp ha
  have hzero : aeval f (p.map (algebraMap ℤ F)) = 0 := by
    rw [aeval_map_algebraMap]
    exact hpf
  have hval : (p.map (algebraMap ℤ F)).eval a = 0 := by
    apply (smul_eq_zero.mp (show (p.map (algebraMap ℤ F)).eval a • v = 0 from ?_)).resolve_right hv0
    rw [← Module.End.aeval_apply_of_hasEigenvector ⟨hv, hv0⟩, hzero, LinearMap.zero_apply]
  exact ⟨p, hp, by simpa only [eval_map, aeval_def] using hval⟩

theorem integral_characteristic_coefficient_closed {F V : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    (f : Module.End F V) (hf : IsIntegral ℤ f) (n : ℕ) : IsIntegral ℤ (f.charpoly.coeff n) := by
  apply Polynomial.isIntegral_coeff_of_factors f.charpoly
  · rw [f.charpoly_monic.leadingCoeff]
    exact isIntegral_one
  · exact IsAlgClosed.splits _
  · intro a ha
    exact integral_eigenvalue f hf a ((Module.End.hasEigenvalue_iff_isRoot_charpoly f a).mpr ha)

theorem integral_characteristic_coefficient {F V : Type*} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    (f : Module.End F V) (hf : IsIntegral ℤ f) (n : ℕ) : IsIntegral ℤ (f.charpoly.coeff n) := by
  let A := AlgebraicClosure F
  have h := integral_characteristic_coefficient_closed (f.baseChange A)
    (hf.map ((Module.End.baseChangeHom F A V).restrictScalars ℤ)) n
  rw [LinearMap.charpoly_baseChange, Polynomial.coeff_map] at h
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F A) (algebraMap F A).injective).mp h

end

end OAI.RepresentationTheory.Theta.Geometric.IntegralCharacteristicCoefficients
