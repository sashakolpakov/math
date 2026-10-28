import OAI.RepresentationTheory.Weil.Local.UnitaryInner
import OAI.RepresentationTheory.Weil.Local.ModulationMeasure

/-! # Density Measure -/

namespace OAI.RepresentationTheory.Weil.Local.DensityMeasure.Construction

noncomputable section

/-! L²-energy preservation and commutation with modulations determine the
pointwise norm, through finite measures with density equal to norm squared. -/

open _root_.MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable (F : Type) [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {d : ℕ}

def testDensityMeasure (f : FunctionsMetaplectic.Construction.schwartzBruhat F d) : Measure (FunctionsMetaplectic.Construction.Position F d) :=
  (UnitaryInner.Construction.referencePositionMeasure F d).withDensity (fun x => ENNReal.ofReal (‖f.val x‖ ^ 2))

instance testDensityMeasure_finite (f : FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    IsFiniteMeasure (testDensityMeasure F f) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => sq_nonneg ‖f.val x‖))).mp
    (FunctionsMetaplectic.Construction.schwartzBruhat_norm_sq_integrable (UnitaryInner.Construction.referencePositionMeasure F d) f).hasFiniteIntegral

theorem testDensityMeasure_integral (f : FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (g : FunctionsMetaplectic.Construction.Position F d → ℂ) :
    ∫ x, g x ∂ testDensityMeasure F f =
      ∫ x, (‖f.val x‖ ^ 2 : ℝ) • g x ∂ UnitaryInner.Construction.referencePositionMeasure F d := by
  unfold testDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (sq_nonneg _)]
  · exact ((FunctionsMetaplectic.Construction.schwartzBruhat_continuous f.property).norm.pow 2).measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem testDensityMeasure_modulation
    (ψ : AddChar F ℂ) (p : FunctionsMetaplectic.Construction.Position F d) (f g : FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hg : ∀ x, g.val x = ModulationMeasure.Construction.modulationCharacter ψ p x * f.val x) :
    ∫ x, ModulationMeasure.Construction.modulationCharacter ψ p x ∂ testDensityMeasure F f =
      ⟪UnitaryInner.Construction.testToL2 F d f, UnitaryInner.Construction.testToL2 F d g⟫_ℂ := by
  rw [testDensityMeasure_integral, UnitaryInner.Construction.testToL2_inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hg, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    change ((‖f.val x‖ ^ 2 : ℝ) : ℂ) * ModulationMeasure.Construction.modulationCharacter ψ p x = _
    exact mul_comm _ _

theorem energy_commutant_preserves_norm [CompleteSpace F]
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
    (hunit : ∀ t, ‖ψ t‖ = 1) (hnontrivial : ∃ t, ψ t ≠ 1)
    (M : FunctionsMetaplectic.Construction.Position F d → FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hM : ∀ p f x, (M p f).val x = ModulationMeasure.Construction.modulationCharacter ψ p x * f.val x)
    (A : FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (henergy : ∀ f, FunctionsMetaplectic.Construction.l2Energy F d (A f) = FunctionsMetaplectic.Construction.l2Energy F d f)
    (hA : ∀ p f, A (M p f) = M p (A f))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat F d) (x : FunctionsMetaplectic.Construction.Position F d) : ‖(A f).val x‖ = ‖f.val x‖ := by
  have hmeasure : testDensityMeasure F (A f) = testDensityMeasure F f := by
    apply ModulationMeasure.Construction.measures_eq_of_modulation_integrals ψ hψ hunit hnontrivial
    intro p
    rw [testDensityMeasure_modulation F ψ p (A f) (M p (A f)) (hM p (A f)),
      testDensityMeasure_modulation F ψ p f (M p f) (hM p f), ← hA]
    exact UnitaryInner.Construction.energy_preserving_inner F d A henergy f (M p f)
  have hc (g : FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      Continuous (fun y => ENNReal.ofReal (‖g.val y‖ ^ 2)) :=
    ENNReal.continuous_ofReal.comp ((FunctionsMetaplectic.Construction.schwartzBruhat_continuous g.property).norm.pow 2)
  have hae : (fun y => ENNReal.ofReal (‖(A f).val y‖ ^ 2)) =ᵐ[UnitaryInner.Construction.referencePositionMeasure F d]
      (fun y => ENNReal.ofReal (‖f.val y‖ ^ 2)) :=
    (withDensity_eq_iff_of_sigmaFinite (hc (A f)).measurable.aemeasurable
      (hc f).measurable.aemeasurable).mp hmeasure
  have heq := congrFun (Measure.eq_of_ae_eq hae (hc (A f)) (hc f)) x
  have hsquare := congrArg ENNReal.toReal heq
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hsquare
  nlinarith [norm_nonneg ((A f).val x), norm_nonneg (f.val x)]

end

end OAI.RepresentationTheory.Weil.Local.DensityMeasure.Construction
