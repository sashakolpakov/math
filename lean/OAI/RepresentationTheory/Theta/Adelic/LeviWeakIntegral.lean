import OAI.RepresentationTheory.Theta.Adelic.LeviCayleyPhase
import OAI.RepresentationTheory.Theta.Adelic.LeviFourierFiber
import OAI.RepresentationTheory.Theta.Adelic.ShiftedTestProduct
import OAI.RepresentationTheory.Theta.Adelic.LeviPairing

/-! # Levi Weak Integral -/

namespace OAI.RepresentationTheory.Theta.Adelic.LeviWeakIntegral

noncomputable section

/-! Evaluation of the absolutely convergent weak Levi integral by Fourier
inversion in the momentum fibers and the exact position Jacobian. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.LeviCayleyPhase OAI.RepresentationTheory.Theta.Adelic.LeviPairing OAI.RepresentationTheory.Theta.Adelic.LeviFourierFiber OAI.RepresentationTheory.Theta.Adelic.ShiftedTestProduct

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ)
variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)
variable (A U : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (hU : U.val = A.val - 1)

include hU in
omit [CompleteSpace k] [LocallyCompactSpace k] [CharZero k] [MeasurableSpace k]
  [BorelSpace k] [SecondCountableTopology k] in
theorem transformed_position_difference (q : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    (A.val * (U⁻¹).val).mulVec q - q = (U⁻¹).val.mulVec q := by
  have hm : A.val * (U⁻¹).val - 1 = (U⁻¹).val := by
    have h : (A.val - 1) * (U⁻¹).val = 1 := by
      rw [← hU, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [sub_mul, one_mul] at h
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))
  calc
    _ = (A.val * (U⁻¹).val - 1).mulVec q := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    _ = _ := by rw [hm]

include hc hu hn hnd hU

theorem weakWeyl_levi_integral (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (hi : Integrable (fun v => ψ (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (Weil.Local.Generators.Construction.leviSymplectic A)
        (LeviCayleyPhase.levi_openCell N A U hU) v) *
      Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f.val h.val v)
        (Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))) :
    Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
      (Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))
        (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (Weil.Local.Generators.Construction.leviSymplectic A) (LeviCayleyPhase.levi_openCell N A U hU)) f.val h.val =
      (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) / Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) *
        ∫ x, f.val ((A⁻¹).val.mulVec x) * conj (h.val x) ∂ Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ := by
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    (Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn N).2.1
  let μ := Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, Weil.Local.FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let Q := Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (Weil.Local.Generators.Construction.leviSymplectic A) (LeviCayleyPhase.levi_openCell N A U hU)
  let F : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ := fun v => ψ (Q v) * Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f.val h.val v
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N => k)).symm
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)
  have hi' : Integrable (fun z : Weil.Local.FunctionsMetaplectic.Construction.Position k N × Weil.Local.FunctionsMetaplectic.Construction.Position k N => F (e z)) (μ.prod μ) :=
    he.integrable_comp_of_integrable hi
  change (∫ v, F v ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)) = _
  rw [← he.integral_comp e.measurableEmbedding]
  change (∫ z : Weil.Local.FunctionsMetaplectic.Construction.Position k N × Weil.Local.FunctionsMetaplectic.Construction.Position k N, F (e z) ∂μ.prod μ) = _
  rw [integral_prod _ hi']
  have hfiber (q : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
      (∫ p, F (e (q, p)) ∂μ) =
        f.val ((A.val * (U⁻¹).val).mulVec q - q) * conj (h.val ((A.val * (U⁻¹).val).mulVec q)) :=
    LeviFourierFiber.momentum_fiber_inversion ψ μ f.val h.val q ((A.val * (U⁻¹).val).mulVec q)
      (fun p => Q (Sum.elim q p)) (LeviCayleyPhase.cayleyPhase_levi N A U hU q)
      (ShiftedTestProduct.shifted_product_fourier_inversion hnd ψ hc hu hn f h q _)
  simp_rw [hfiber, transformed_position_difference N A U hU]
  let T := U * A⁻¹
  let G : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ := fun x => f.val ((A⁻¹).val.mulVec x) * conj (h.val x)
  have ht (q : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
      f.val ((U⁻¹).val.mulVec q) * conj (h.val ((A.val * (U⁻¹).val).mulVec q)) =
        G ((Weil.Local.LinearSubstitution.Construction.positionAddEquiv T).symm q) := by
    change _ = f.val ((A⁻¹).val.mulVec ((T⁻¹).val.mulVec q)) * conj (h.val ((T⁻¹).val.mulVec q))
    dsimp only [T]
    have hAi : (A⁻¹).val * A.val = 1 := A.inv_val
    rw [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mulVec_mulVec, ← mul_assoc, hAi, one_mul]
  simp_rw [ht]
  rw [LeviPairing.integral_comp_coordinate_inverse_complex μ (Weil.Local.LinearSubstitution.Construction.positionAddEquiv T) G,
    Weil.Local.DeterminantMeasure.Construction.coordinateJacobian_eq_determinant]
  have hd : Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k T = Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U * (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)⁻¹ := by
    change Matrix.GeneralLinearGroup.det (U * A⁻¹) = _
    rw [map_mul, map_inv]
    rfl
  rw [hd, Weil.Local.FunctionsMetaplectic.Construction.localModulus_mul, Weil.Local.FunctionsMetaplectic.Construction.localModulus_inv]
  change ((Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) * (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A))⁻¹ : ℝ) : ℂ) *
      (∫ x, G x ∂μ) =
    ((Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) : ℂ) / (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ)) *
      (∫ x, G x ∂μ)
  rw [Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]

end

end OAI.RepresentationTheory.Theta.Adelic.LeviWeakIntegral
