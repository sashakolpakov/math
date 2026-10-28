import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Corrected Normalization Analysis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis.Construction

noncomputable section

/-! Test pairings determine actual Bruhat operators. The corrected integral
also has the required trivial-character and rank-zero behavior. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem integral_test_pairing_ext
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (he : ∀ u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ x, f.val x * conj (u.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
        ∫ x, h.val x * conj (u.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) : f = h := by
  let P := UnitarySplitting.Weak.Construction.testToL2 k N
  have hi (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : ⟪P u, P f⟫_ℂ = ⟪P u, P h⟫_ℂ := by
    rw [UnitarySplitting.Weak.Construction.testToL2_inner, UnitarySplitting.Weak.Construction.testToL2_inner]
    exact he u
  have hz : ⟪P (f - h), P (f - h)⟫_ℂ = 0 := by
    rw [map_sub, inner_sub_right, ← map_sub, hi, sub_self]
  apply UnitarySplitting.Weak.Construction.testToL2_injective k N
  exact sub_eq_zero.mp (by simpa only [map_sub] using (inner_self_eq_zero.mp hz))

theorem localCover_pairing_ext
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ} {ψ : AddChar k ℂ}
    {a b : Oscillator.Construction.LocalCover k N ψ}
    (hp : Oscillator.Construction.localProjection k N ψ a = Oscillator.Construction.localProjection k N ψ b)
    (ho : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ x, (Oscillator.Construction.localOperator k N ψ a f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      ∫ x, (Oscillator.Construction.localOperator k N ψ b f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N) : a = b := by
  apply Subtype.ext
  apply Prod.ext hp
  apply LinearEquiv.ext
  intro f
  exact integral_test_pairing_ext _ _ (ho f)

theorem correctedWeakOpenCellValue_of_measure_zero
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)
    (hμ : Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ = 0) (N : ℕ) (hN : 0 < N)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ g f h = 0 := by
  have hzero : Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ) = 0 := by
    simp only [hμ]
    apply (Measure.measure_univ_eq_zero).mp
    rw [Measure.pi_univ]
    exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl ⟨0, hN⟩)) rfl
  unfold CorrectedNormalization.Construction.correctedWeakOpenCellValue
  split_ifs <;> simp [CorrectedNormalization.Construction.correctedWeakOpenCell, UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian, hzero]

theorem correctedWeakOpenCellValue_trivial
    (k : Type) [NormedField k] [Infinite k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ) (hψ : ∀ x, ψ x = 1)
    (N : ℕ) (hN : 0 < N) (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ g f h = 0 :=
  correctedWeakOpenCellValue_of_measure_zero k ψ (Normalization.Construction.selfDualMeasure_trivial k ψ hψ) N hN g f h

theorem correctedWeakOpenCellValue_zero_rank
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k 0) (f h : Local.FunctionsMetaplectic.Construction.Position k 0 → ℂ) :
    CorrectedNormalization.Construction.correctedWeakOpenCellValue k 0 ψ g f h =
      ∫ x, f x * conj (h x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k 0 := by
  have hg : (g.val - 1).det ≠ 0 := by simp [Matrix.det_isEmpty]
  have hs : Normalization.Construction.openCellScale k 0 g = 1 := by
    simp [Normalization.Construction.openCellScale, Matrix.det_isEmpty, Local.FunctionsMetaplectic.Construction.localModulus_one]
  rw [CorrectedNormalization.Construction.correctedWeakOpenCellValue_open k 0 ψ g hg]
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
  rw [hs, Complex.ofReal_one, inv_one, one_mul, Measure.pi_of_empty _ (0 : Local.FunctionsMetaplectic.Construction.PhaseSpace k 0)]
  simp only [integral_dirac]
  have hq : SchrodingerPairing.Construction.schrodingerCayleyPhase k 0 g hg 0 = 0 := by
    simp [SchrodingerPairing.Construction.schrodingerCayleyPhase, UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase]
  rw [hq, ψ.map_zero_eq_one, one_mul]
  unfold UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [Local.FunctionsMetaplectic.Construction.heisenbergFunction]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis.Construction
