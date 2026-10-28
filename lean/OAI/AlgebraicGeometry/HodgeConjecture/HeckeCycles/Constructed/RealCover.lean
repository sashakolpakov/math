import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerKernel
import OAI.RepresentationTheory.Weil.Local.UnitaryInner

/-! # Real Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover.CM

noncomputable section

/-! Construct the real Schrödinger cover required by PoissonAutomorphy from LocalWeil's
actual bare metaplectic group. All projection, kernel, intertwining,
and unitary properties are proved for the unchanged test functions. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Weil.Local.UnitaryInner.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerKernel.CM

theorem unitary (n : ℕ) (g : Real.SchrodingerAction.CM.RealMp n) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) :
    (∫ x, (Real.SchrodingerAction.CM.action n g f).val x * star ((Real.SchrodingerAction.CM.action n g h).val x)) =
      ∫ x, f.val x * star (h.val x) := by
  have he := RepresentationTheory.Weil.Local.UnitaryInner.Construction.energy_preserving_inner ℝ n (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g).toLinearMap
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation_unitary ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g) (Real.SchwartzComparison.CM.tests n h) (Real.SchwartzComparison.CM.tests n f)
  rw [RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_inner, RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2_inner] at he
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure] at he
  let c := Measure.addHaarScalarFactor (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume
  have hc : (c : ℝ) ≠ 0 := by
    exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume).ne'
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  change (c : ℂ) * (∫ x, (Real.SchrodingerAction.CM.action n g f).val x * star ((Real.SchrodingerAction.CM.action n g h).val x)) =
    (c : ℂ) * (∫ x, f.val x * star (h.val x)) at he
  exact mul_left_cancel₀ hc' he

def realCover (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (Real.SchrodingerAction.CM.RealMp n) where
  project := Real.SchrodingerAction.CM.projection n
  action := Real.SchrodingerAction.CM.action n
  surjective := Real.SchrodingerAction.CM.projection_surjective n
  negOne := Real.SchrodingerKernel.CM.negOne n
  negOne_ne_one := Real.SchrodingerKernel.CM.negOne_ne_one n
  project_negOne := Real.SchrodingerKernel.CM.project_negOne n
  kernel := Real.SchrodingerKernel.CM.kernel n
  genuine := Real.SchrodingerKernel.CM.genuine n
  faithful := Real.SchrodingerKernel.CM.faithful n
  intertwines := Real.SchrodingerAction.CM.action_intertwines n
  unitary := CM.unitary n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.RealCover.CM
