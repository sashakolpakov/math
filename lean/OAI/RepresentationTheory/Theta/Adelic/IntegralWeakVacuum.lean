import OAI.RepresentationTheory.Theta.Adelic.IntegralCayleyPhase
import OAI.RepresentationTheory.Theta.Adelic.UnramifiedVacuumFourier
import OAI.RepresentationTheory.Theta.Adelic.VacuumPairing
import OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

/-! # Integral Weak Vacuum -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralWeakVacuum

noncomputable section

/-! Exact evaluation of the corrected weak Cayley integral on the
standard vacuum for every unimodular integral open-cell matrix. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.IntegralCayleyPhase OAI.RepresentationTheory.Theta.Adelic.UnramifiedVacuumFourier

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
local instance : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ℂ)
variable [(Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ψ).IsAddHaarMeasure]
variable (hF : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ)
  (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val)
variable (hFF : Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (N + N) ψ)
  (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val = (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val)
variable (hψ : ∀ t ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v), ψ t = 1)
variable (hhalf : (2 : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
variable (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
variable (D : (Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)))ˣ)
variable (hD : D.val = g.val - 1)
variable (hv : ∀ i j, D.val i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
variable (hi : ∀ i j, D.inv i j ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))

include hD hi hψ hhalf in
omit [(Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ψ).IsAddHaarMeasure] in
theorem vacuum_cayley_phase (w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
    ψ (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N g (IntegralCayleyPhase.integral_difference_open N g D hD) w) *
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val (Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N w) =
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val (Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N w) := by
  rw [Weil.AdelicSplitting.WeylVacuum.Construction.finiteVacuum_phaseCoordinates]
  by_cases hq : ∀ i, Weil.UnitarySplitting.FourierCovariance.Construction.phasePosition w i ∈ v.adicCompletionIntegers F
  · by_cases hp : ∀ i, Weil.UnitarySplitting.FourierCovariance.Construction.phaseMomentum w i ∈ v.adicCompletionIntegers F
    · have hw : ∀ i, w i ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) := by
        intro i
        cases i with
        | inl i => exact hq i
        | inr i => exact hp i
      rw [hψ _ (IntegralCayleyPhase.cayleyPhase_integral N g D hD _ hhalf hi w hw), one_mul]
    · rw [Weil.AdelicSplitting.FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hp, mul_zero, mul_zero]
  · rw [Weil.AdelicSplitting.FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hq, zero_mul, mul_zero]

include hFF in
theorem doubled_vacuum_phase_integral :
    (∫ w, (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val (Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N w)
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ψ)) = 1 := by
  have he := Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates_measurePreserving (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N
    (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) ψ)
  calc
    _ = ∫ x, (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val x
        ∂ Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (N + N) ψ :=
      he.integral_comp (Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N).toHomeomorph.measurableEmbedding _
    _ = 1 := UnramifiedVacuumFourier.vacuum_integral_of_fourier F (N + N) v ψ _ hFF

include hF hFF hψ hhalf hD hv hi in
theorem correctedWeakOpenCellValue_integral_vacuum :
    Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ g
      (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val =
      (Weil.Local.FunctionsMetaplectic.Construction.l2Energy (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : ℂ) := by
  have hSc : IsCompact (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) := by
    have he : (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))) = Metric.closedBall 0 1 := by
      ext x
      simp only [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
      rfl
    rw [he]
    exact isCompact_closedBall _ _
  have hs := IntegralCayleyPhase.openCellScale_integral N g D hD (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v))
    (IntegralTopology.localIntegerRing_open F (.inr v)) hSc hv hi
  let : (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ).IsAddHaarMeasure := by
    dsimp [Weil.Local.FunctionsMetaplectic.Construction.positionMeasure]
    infer_instance
  rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue_open _ N ψ g (IntegralCayleyPhase.integral_difference_open N g D hD)]
  unfold Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCell
  rw [hs, Complex.ofReal_one, inv_one, one_mul]
  unfold Weil.UnitarySplitting.WeakWeylGaussian.Construction.weakWeylGaussian
  have hp (w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N) :
      ψ (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N g (IntegralCayleyPhase.integral_difference_open N g D hD) w) *
        Weil.UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ
          (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
          (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val w =
      (Weil.Local.FunctionsMetaplectic.Construction.l2Energy (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : ℂ) *
        (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (N + N) v).val (Weil.AdelicSplitting.PhaseMeasure.Construction.phaseCoordinates (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N w) := by
    rw [UnramifiedVacuumFourier.vacuum_reference_weyl_coefficient F N v ψ hF hψ hhalf,
      mul_left_comm, vacuum_cayley_phase F N v ψ hψ hhalf g D hD hi]
  simp_rw [hp]
  rw [integral_const_mul, doubled_vacuum_phase_integral F N v ψ hFF, mul_one]

include hF hFF hψ hhalf hD hv hi in
theorem oscillator_fixes_integral_vacuum (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ)
    (hnorm : (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ a (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)).val x *
      conj ((Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N) =
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ g
        (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N ψ a (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  apply VacuumPairing.oscillator_fixes_of_pairing N ψ a
  exact hnorm.trans (correctedWeakOpenCellValue_integral_vacuum F N v ψ hF hFF hψ hhalf g D hD hv hi)

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralWeakVacuum
