import OAI.RepresentationTheory.Theta.Adelic.IntegralModulus
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization

/-! # Integral Cayley Phase -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralCayleyPhase

noncomputable section

/-! On a unimodular integral open cell, the corrected Cayley phase is
integral on the phase lattice and its Haar normalization is one. -/

open _root_.Matrix

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction OAI.RepresentationTheory.Theta.Adelic.IntegralModulus

variable {k : Type} [NormedField k] (N : ℕ)
variable (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N)
variable (D : (Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k)ˣ)
variable (hD : D.val = g.val - 1)

include hD in
theorem integral_difference_open : (g.val - 1).det ≠ 0 := by
  rw [← hD]
  exact (Matrix.GeneralLinearGroup.det D).ne_zero

include hD in
theorem inverseDifference_eq (w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g (integral_difference_open N g D hD)).symm w = D.inv *ᵥ w := by
  apply (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g (integral_difference_open N g D hD)).injective
  rw [LinearEquiv.apply_symm_apply, Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply]
  change w = g.val *ᵥ (D.inv *ᵥ w) - D.inv *ᵥ w
  calc
    w = D.val *ᵥ (D.inv *ᵥ w) := by rw [mulVec_mulVec, D.val_inv, one_mulVec]
    _ = _ := by rw [hD, sub_mulVec, one_mulVec]

include hD in
theorem cayleyPhase_integral (S : Subring k) (hhalf : (2 : k)⁻¹ ∈ S)
    (hi : ∀ i j, D.inv i j ∈ S) (w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (hw : ∀ i, w i ∈ S) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N g (integral_difference_open N g D hD) w ∈ S := by
  change Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k N
    ((Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g (integral_difference_open N g D hD)).symm w) w / 2 ∈ S
  rw [inverseDifference_eq N g D hD, div_eq_mul_inv]
  apply S.mul_mem _ hhalf
  rw [Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
  apply S.sum_mem
  intro i _
  exact S.sub_mem
    (S.mul_mem (IntegralModulus.integral_mulVec S hi hw (.inr i)) (hw (.inl i)))
    (S.mul_mem (IntegralModulus.integral_mulVec S hi hw (.inl i)) (hw (.inr i)))

variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]

include hD in
theorem openCellScale_integral (S : Subring k)
    (hSo : IsOpen (S : Set k)) (hSc : IsCompact (S : Set k))
    (hv : ∀ i j, D.val i j ∈ S) (hi : ∀ i j, D.inv i j ∈ S) :
    Weil.AdelicSplitting.Normalization.Construction.openCellScale k N g = 1 := by
  have hmod : Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Matrix.GeneralLinearGroup.det D) = 1 :=
    IntegralModulus.localModulus_integral_unit S hSo hSc (Matrix.GeneralLinearGroup.det D)
      (IntegralModulus.integral_determinant S hv) (IntegralModulus.integral_determinant S hi)
  rw [Weil.AdelicSplitting.Normalization.Construction.openCellScale, dite_eq_left (integral_difference_open N g D hD)]
  have he : Units.mk0 (g.val - 1).det (integral_difference_open N g D hD) =
      Matrix.GeneralLinearGroup.det D := by
    apply Units.ext
    exact congrArg Matrix.det hD.symm
  rw [he, hmod, Real.sqrt_one]

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralCayleyPhase
