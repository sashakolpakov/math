import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylAnalysis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesisCovariance
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Weyl Resolution Operator -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator.Construction

noncomputable section

section

/-! An actual Bruhat-space operator obtained by Weyl analysis followed by
Weyl synthesis. It commutes with the entire Weyl representation. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

section Test

variable {F : Type} [NormedField F] [LocallyCompactSpace F] [IsUltrametricDist F]
variable [MeasurableSpace F] [BorelSpace F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
variable (hn : ∃ x : F, ψ x ≠ 1)

include hF hc in
theorem weylAnalysis_locallyConstant (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    IsLocallyConstant (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val) :=
  (UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hF ψ hc (Weak.Construction.referencePositionMeasure F d) u f).comp conj

include hF hn in
theorem weylAnalysis_compactSupport (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    HasCompactSupport (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  exact (WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn (Weak.Construction.referencePositionMeasure F d) u f).comp_left
    (map_zero conj)

def ultraResolutionTest (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  ⟨WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val) u.val,
    WeylSynthesisAdd.Construction.weylSynthesis_mem_ultra hF ψ hc ν _ (weylAnalysis_locallyConstant hF ψ hc u f)
      (weylAnalysis_compactSupport hF ψ hn u f) u⟩

theorem ultraResolutionTest_apply (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    (ultraResolutionTest hF ψ hc hn ν u f).val =
      WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val f.val) u.val := rfl

end Test

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
variable [CharZero F] [IsUltrametricDist F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure] (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)

def ultraResolutionLinearMap : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun := ultraResolutionTest hF ψ hc hn ν u
  map_add' f h := by
    apply Subtype.ext
    change (ultraResolutionTest hF ψ hc hn ν u (f + h)).val =
      (ultraResolutionTest hF ψ hc hn ν u f).val + (ultraResolutionTest hF ψ hc hn ν u h).val
    rw [ultraResolutionTest_apply, ultraResolutionTest_apply, ultraResolutionTest_apply,
      WeylAnalysis.Construction.weylAnalysis_add hF ψ hc hu]
    exact WeylSynthesisAdd.Construction.weylSynthesis_add ψ hc ν _ _
      (weylAnalysis_locallyConstant hF ψ hc u f).continuous
      (weylAnalysis_locallyConstant hF ψ hc u h).continuous
      (weylAnalysis_compactSupport hF ψ hn u f) (weylAnalysis_compactSupport hF ψ hn u h) u
  map_smul' z f := by
    apply Subtype.ext
    change (ultraResolutionTest hF ψ hc hn ν u (z • f)).val =
      z • (ultraResolutionTest hF ψ hc hn ν u f).val
    rw [ultraResolutionTest_apply, ultraResolutionTest_apply,
      WeylAnalysis.Construction.weylAnalysis_smul hF ψ hc hu, WeylSynthesisAdd.Construction.weylSynthesis_smul]

theorem ultraResolutionLinearMap_commutes (w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ultraResolutionLinearMap hF ψ hc hu hn ν u (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w (ultraResolutionLinearMap hF ψ hc hu hn ν u f) := by
  apply Subtype.ext
  change (ultraResolutionTest hF ψ hc hn ν u (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f)).val =
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ w (ultraResolutionTest hF ψ hc hn ν u f).val
  rw [ultraResolutionTest_apply, ultraResolutionTest_apply, WeylSynthesisCovariance.Construction.weylSynthesis_heisenberg]
  congr 1
  funext v
  exact WeylAnalysis.Construction.weylAnalysis_input_shift hF ψ hc hu u f v w

end

/-! Weyl analysis followed by synthesis is a positive nonzero scalar
multiple of the identity on the nonarchimedean Bruhat space. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F]
variable [CharZero F] [IsUltrametricDist F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
variable (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)

omit [CompleteSpace F] [CharZero F] [IsUltrametricDist F] in
theorem testToL2_ne_zero (hu0 : u ≠ 0) : Weak.Construction.testToL2 F d u ≠ 0 := by
  intro hh
  apply hu0
  apply Weak.Construction.testToL2_injective F d
  simpa only [map_zero] using hh

include hF hc hu in
omit [IsUltrametricDist F] in
theorem weylMatrixCoefficient_self_zero_ne_zero (hu0 : u ≠ 0) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val 0 ≠ 0 := by
  have hρ0 : HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu 0 u = u := Subtype.ext (Heisenberg.Construction.heisenbergFunction_zero ψ u.val)
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, hρ0, inner_self_eq_norm_sq_to_K]
  change (‖Weak.Construction.testToL2 F d u‖ : ℂ) ^ 2 ≠ 0
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (testToL2_ne_zero u hu0)))

include hF hc hu hn in
theorem weylMatrixCoefficient_self_energy_pos (hu0 : u ≠ 0) :
    0 < ∫ v, ‖WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val v‖ ^ 2 ∂ν := by
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val
  have hCc : Continuous C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu (Weak.Construction.referencePositionMeasure F d) u u
  have hCs : HasCompactSupport C :=
    WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn (Weak.Construction.referencePositionMeasure F d) u u
  have hIc : Continuous (fun v => ‖C v‖ ^ 2) := hCc.norm.pow 2
  have hIs : HasCompactSupport (fun v => ‖C v‖ ^ 2) :=
    hCs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hIi : Integrable (fun v => ‖C v‖ ^ 2) ν := hIc.integrable_of_hasCompactSupport
    hIs
  exact integral_pos_of_integrable_nonneg_nonzero (x := (0 : Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) hIc hIi (fun _ => sq_nonneg _)
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (weylMatrixCoefficient_self_zero_ne_zero hF ψ hc hu u hu0)))

theorem ultraResolution_self_pairing :
    ⟪Weak.Construction.testToL2 F d u, Weak.Construction.testToL2 F d (ultraResolutionLinearMap hF ψ hc hu hn ν u u)⟫_ℂ =
      ((∫ v, ‖WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val v‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val
    rw [Weak.Construction.testToL2_inner]
    change (∫ x, WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val)
      u.val x * conj (u.val x) ∂ Weak.Construction.referencePositionMeasure F d) = _
    rw [WeylSynthesis.Construction.weylSynthesis_pairing ψ hc hu (Weak.Construction.referencePositionMeasure F d) ν _
      (weylAnalysis_locallyConstant hF ψ hc u u).continuous
      ((weylAnalysis_locallyConstant hF ψ hc u u).continuous.integrable_of_hasCompactSupport
        (weylAnalysis_compactSupport hF ψ hn u u))]
    change (∫ v, conj (C v) * C v ∂ν) = _
    have hnorm (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : conj (C v) * C v = ((‖C v‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hnorm]
    exact integral_complex_ofReal (μ := ν) (f := fun v => ‖C v‖ ^ 2)

theorem ultraResolution_scalar :
    ∃ z : ℂ, ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      ultraResolutionLinearMap hF ψ hc hu hn ν u f = z • f := by
  exact UltraMultiplier.Construction.ultra_commutant_scalar hF ψ hc hn hu (ultraResolutionLinearMap hF ψ hc hu hn ν u)
    (fun v f => ultraResolutionLinearMap_commutes hF ψ hc hu hn ν u v f)

theorem ultraResolution_positive_scalar (hu0 : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      ultraResolutionLinearMap hF ψ hc hu hn ν u f = (r : ℂ) • f := by
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val
  obtain ⟨z, hz⟩ := ultraResolution_scalar hF ψ hc hu hn ν u
  have hLu := testToL2_ne_zero u hu0
  have hIpos := weylMatrixCoefficient_self_energy_pos hF ψ hc hu hn ν u hu0
  have hp := ultraResolution_self_pairing hF ψ hc hu hn ν u
  let r := (∫ v, ‖C v‖ ^ 2 ∂ν) / ‖Weak.Construction.testToL2 F d u‖ ^ 2
  have hr : 0 < r := div_pos hIpos (sq_pos_of_pos (norm_pos_iff.mpr hLu))
  have hzr : z = (r : ℂ) := by
    rw [hz, map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K] at hp
    change z = ((∫ v, ‖C v‖ ^ 2 ∂ν) / ‖Weak.Construction.testToL2 F d u‖ ^ 2 : ℝ)
    rw [Complex.ofReal_div, Complex.ofReal_pow]
    apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hLu)))).mpr
    exact hp
  exact ⟨r, hr, fun f => hzr ▸ hz f⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator.Construction
