import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi
import OAI.RepresentationTheory.Weil.Local.LinearIntertwiner
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylMatrixCoefficients

/-! # Levi Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.LeviPairing

noncomputable section

/-! Continuous raw substitution pairings and their exact Haar adjoint.
The test vector in the second slot supplies a uniform integrable bound. -/

open _root_.MeasureTheory Filter
open scoped ComplexConjugate _root_.Topology InnerProductSpace

open OAI.RepresentationTheory.Weil.Local.LinearIntertwiner.Construction

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}

def rawPairing (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : ℂ :=
  ∫ x, f.val ((A⁻¹).val.mulVec x) * conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N

theorem rawPairing_continuous (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Continuous (fun A => rawPairing A f h) := by
  let : FirstCountableTopology (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (FirstCountableTopology (Fin N → Fin N → k))
  let : FirstCountableTopology (Matrix (Fin N) (Fin N) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  let : FirstCountableTopology (Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) := Units.isInducing_embedProduct.firstCountableTopology
  obtain ⟨C, -, hC⟩ := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.schwartzBruhat_norm_bound f.property
  have hfc := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.schwartzBruhat_continuous f.property
  have hhc := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.schwartzBruhat_continuous h.property
  have hcont : Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N × Weil.Local.FunctionsMetaplectic.Construction.Position k N =>
      f.val ((p.1⁻¹).val.mulVec p.2) * conj (h.val p.2)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  rw [continuous_iff_continuousAt]
  intro A
  apply tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖h.val x‖)
  · exact Filter.Eventually.of_forall fun B =>
      (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun B => Filter.Eventually.of_forall fun x => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · exact (Weil.UnitarySplitting.TestSpaceAnalysis.Construction.schwartzBruhat_integrable (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) h).norm.const_mul C
  · exact Filter.Eventually.of_forall fun x =>
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

theorem integral_comp_coordinate_inverse_complex
    (μ : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (e : Weil.Local.FunctionsMetaplectic.Construction.Position k N ≃ₜ+ Weil.Local.FunctionsMetaplectic.Construction.Position k N) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    (∫ x, f (e.symm x) ∂μ) = (Weil.Local.LinearSubstitution.Construction.coordinateJacobian e : ℂ) * ∫ x, f x ∂μ := by
  let em := e.toHomeomorph.toMeasurableEquiv
  calc
    _ = ∫ x, f x ∂(μ.map em.symm) := (integral_map_equiv em.symm f).symm
    _ = ∫ x, f x ∂(μ.comap em) := by rw [em.map_symm]
    _ = _ := by
      change (∫ x, f x ∂μ.comap e) = (Weil.Local.LinearSubstitution.Construction.coordinateJacobian e : ℂ) * ∫ x, f x ∂μ
      rw [← addEquivAddHaarChar_smul_eq_comap μ e, integral_smul_nnreal_measure]
      rfl

theorem rawPairing_adjoint (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    rawPairing A f h = (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * conj (rawPairing A⁻¹ h f) := by
  let e := Weil.Local.LinearSubstitution.Construction.positionAddEquiv A
  have he (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) : e (e.symm x) = x := e.apply_symm_apply x
  have hi := integral_comp_coordinate_inverse_complex (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) e
    (fun x => f.val x * conj (h.val (e x)))
  simp only [he] at hi
  rw [Weil.Local.DeterminantMeasure.Construction.coordinateJacobian_eq_determinant] at hi
  change rawPairing A f h = _ at hi
  rw [hi]
  congr 1
  rw [rawPairing, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [inv_inv, map_mul, starRingEnd_self_apply]
    change f.val x * conj (h.val (A.val.mulVec x)) = conj (h.val (A.val.mulVec x)) * f.val x
    ring

theorem rawPairing_self_image (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    rawPairing A f (Weil.Local.LinearSubstitution.Construction.testSubstitution A f) =
      ⟪Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.Local.LinearSubstitution.Construction.testSubstitution A f), Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.Local.LinearSubstitution.Construction.testSubstitution A f)⟫_ℂ := by
  rw [Weil.UnitarySplitting.Weak.Construction.testToL2_inner]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.LeviPairing
