import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCayleyIsometry
import OAI.RepresentationTheory.Weil.AdelicSplitting.EnergyIntertwinerRealization
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator

/-! # Real Weak Unitary -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RealWeakUnitary.Construction

noncomputable section

/-! Exact unitary normalization of the real weak Cayley integral on the
actual Bruhat space, with no unproved normalization premise. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator.Construction
  (realCayleyOperator)
open scoped InnerProductSpace ComplexConjugate

variable {N : ℕ} (hk : ¬ DiscreteTopology ℝ) (ψ : AddChar ℝ ℂ)
variable (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ N)) [ν.IsAddHaarMeasure]
variable (g : Local.FunctionsMetaplectic.Construction.Symplectic ℝ N) (hg : (g.val - 1).det ≠ 0)

def correctedRealCayleyTestOperator : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N :=
  (Normalization.Construction.openCellScale ℝ N g : ℂ)⁻¹ • UnitarySplitting.RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ N g) (SchrodingerPairing.Construction.openCellDifference ℝ N g hg) (SchrodingerPairing.Construction.openCellDifference_apply ℝ N g hg)

theorem correctedRealCayleyTestOperator_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    ⟪UnitarySplitting.Weak.Construction.testToL2 ℝ N h,
      UnitarySplitting.Weak.Construction.testToL2 ℝ N (correctedRealCayleyTestOperator ψ hc hu hn ν g hg f)⟫_ℂ =
        CorrectedNormalization.Construction.correctedWeakOpenCell ℝ N ψ ν g hg f.val h.val := by
  change ⟪_, UnitarySplitting.Weak.Construction.testToL2 ℝ N ((Normalization.Construction.openCellScale ℝ N g : ℂ)⁻¹ • _)⟫_ℂ = _
  rw [map_smul, inner_smul_right]
  unfold CorrectedNormalization.Construction.correctedWeakOpenCell SchrodingerPairing.Construction.schrodingerCayleyPhase
  rw [CorrectedNormalization.Construction.schrodingerPairing_eq_standardBilinear]
  congr 1
  exact UnitarySplitting.RealCayleyOperator.Construction.realCayleyOperator_pairing ψ hc hu hn ν
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ N g) (SchrodingerPairing.Construction.openCellDifference ℝ N g hg) (SchrodingerPairing.Construction.openCellDifference_apply ℝ N g hg) f h

theorem correctedRealCayleyTestOperator_covariance (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ N) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
    correctedRealCayleyTestOperator ψ hc hu hn ν g hg (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
      UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v)
        (correctedRealCayleyTestOperator ψ hc hu hn ν g hg f) := by
  change (Normalization.Construction.openCellScale ℝ N g : ℂ)⁻¹ • _ =
    UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu (Local.FunctionsMetaplectic.Construction.symplecticAction g v) ((Normalization.Construction.openCellScale ℝ N g : ℂ)⁻¹ • _)
  rw [map_smul]
  congr 1
  exact UnitarySplitting.RealCayleyOperator.Construction.realCayleyOperator_intertwines ψ hc hu hn ν
    (CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ N g) (SchrodingerPairing.Construction.openCellDifference ℝ N g hg) (SchrodingerPairing.Construction.openCellDifference_apply ℝ N g hg) v f

include hk hc hu hn in
theorem correctedWeakOpenCell_real_unitary :
    ∃ U : Oscillator.Construction.LocalCover ℝ N ψ, Oscillator.Construction.localProjection ℝ N ψ U = g ∧
      ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N,
        CorrectedNormalization.Construction.correctedWeakOpenCell ℝ N ψ (Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ))
          g hg f.val h.val =
        ∫ x, (Oscillator.Construction.localOperator ℝ N ψ U f).val x * conj (h.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ N := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ
    (RealNormalization.LocalAnalysis.real_fourier_analysis N ψ hc hu hn).1
  let μ := Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
  let A := correctedRealCayleyTestOperator ψ hc hu hn μ g hg
  obtain ⟨M, hM, hMp⟩ := ArchimedeanCayleyIsometry.Construction.correctedWeakOpenCell_real_hilbert_isometry hk ψ hc hu hn g hg
  have hPA (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) :
      UnitarySplitting.Weak.Construction.testToL2 ℝ N (A f) = M (UnitarySplitting.Weak.Construction.testToL2 ℝ N f) := by
    apply DenseHilbert.Construction.eq_of_dense_test_pairings (UnitarySplitting.Weak.Construction.testToL2 ℝ N) (ArchimedeanSpace.Construction.archimedean_testToL2_dense N)
    intro h
    rw [hMp]
    exact correctedRealCayleyTestOperator_pairing ψ hc hu hn μ g hg f h
  have hA (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N) : Local.FunctionsMetaplectic.Construction.l2Energy ℝ N (A f) = Local.FunctionsMetaplectic.Construction.l2Energy ℝ N f := by
    have he := congrArg (fun x : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ N) => ‖x‖ ^ 2) (hPA f)
    rw [hM.norm_map_of_map_zero (map_zero M), UnitarySplitting.Weak.Construction.testToL2_norm,
      UnitarySplitting.Weak.Construction.testToL2_norm,
      Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy ℝ N (A f) from integral_nonneg (fun x => sq_nonneg ‖(A f).val x‖)),
      Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy ℝ N f from integral_nonneg (fun x => sq_nonneg ‖f.val x‖))] at he
    exact he
  obtain ⟨a, ha⟩ := LocalSurjectivity.Construction.localProjection_surjective_real ψ hu hc hn g
  obtain ⟨U, hU, hUA⟩ := EnergyIntertwinerRealization.Construction.energy_intertwiner_local_realization hk ψ hc hu hn g A hA
    (correctedRealCayleyTestOperator_covariance hk ψ hc hu hn μ g hg) a ha
  refine ⟨U, hU, fun f h => ?_⟩
  rw [hUA, ← UnitarySplitting.Weak.Construction.testToL2_inner]
  exact (correctedRealCayleyTestOperator_pairing ψ hc hu hn μ g hg f h).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RealWeakUnitary.Construction
