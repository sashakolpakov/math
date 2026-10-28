import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.IntegralPair
import Mathlib.Analysis.InnerProductSpace.Defs

/-! # Inner Product -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.InnerProduct

noncomputable section

/-! The actual metric integral supplies an inner-product core on smooth sections of the constructed holomorphic line bundle. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

instance holomorphicLineSmoothForm_addCommGroup {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (n : ℕ) :
    AddCommGroup (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) := Module.addCommMonoidToAddCommGroup ℂ

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

theorem holomorphicLineSectionIntegralPair_conj (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    conj (IntegralPair.holomorphicLineSectionIntegralPair V u s t) = IntegralPair.holomorphicLineSectionIntegralPair V u t s := by
  unfold IntegralPair.holomorphicLineSectionIntegralPair
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [IntegralPair.holomorphicLineGlobalSectionPair_apply, HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair_conj]

theorem holomorphicLineSectionIntegralPair_add_right (s t r : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    IntegralPair.holomorphicLineSectionIntegralPair V u s (t + r) =
      IntegralPair.holomorphicLineSectionIntegralPair V u s t + IntegralPair.holomorphicLineSectionIntegralPair V u s r := by
  calc
    _ = ∫ x, (IntegralPair.holomorphicLineGlobalSectionPair V u s t x + IntegralPair.holomorphicLineGlobalSectionPair V u s r x)
        ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [IntegralPair.holomorphicLineGlobalSectionPair_apply, HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair_add_right]
    _ = _ := integral_add (IntegralPair.holomorphicLineGlobalSectionPair_integrable V u s t)
      (IntegralPair.holomorphicLineGlobalSectionPair_integrable V u s r)

theorem holomorphicLineSectionIntegralPair_smul_right (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (z : ℂ) :
    IntegralPair.holomorphicLineSectionIntegralPair V u s (z • t) = z * IntegralPair.holomorphicLineSectionIntegralPair V u s t := by
  calc
    _ = ∫ x, z * IntegralPair.holomorphicLineGlobalSectionPair V u s t x ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [IntegralPair.holomorphicLineGlobalSectionPair_apply, HolomorphicSmooth.SectionPair.holomorphicLineSmoothSectionPair_smul_right]
    _ = _ := integral_const_mul z _

theorem holomorphicLineSectionIntegralPair_add_left (s t r : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    IntegralPair.holomorphicLineSectionIntegralPair V u (s + t) r =
      IntegralPair.holomorphicLineSectionIntegralPair V u s r + IntegralPair.holomorphicLineSectionIntegralPair V u t r := by
  calc
    _ = conj (IntegralPair.holomorphicLineSectionIntegralPair V u r (s + t)) :=
      (holomorphicLineSectionIntegralPair_conj V u r (s + t)).symm
    _ = conj (IntegralPair.holomorphicLineSectionIntegralPair V u r s + IntegralPair.holomorphicLineSectionIntegralPair V u r t) := by
      rw [holomorphicLineSectionIntegralPair_add_right]
    _ = _ := by rw [map_add, holomorphicLineSectionIntegralPair_conj, holomorphicLineSectionIntegralPair_conj]

theorem holomorphicLineSectionIntegralPair_smul_left (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (z : ℂ) :
    IntegralPair.holomorphicLineSectionIntegralPair V u (z • s) t =
      conj z * IntegralPair.holomorphicLineSectionIntegralPair V u s t := by
  calc
    _ = conj (IntegralPair.holomorphicLineSectionIntegralPair V u t (z • s)) :=
      (holomorphicLineSectionIntegralPair_conj V u t (z • s)).symm
    _ = conj (z * IntegralPair.holomorphicLineSectionIntegralPair V u t s) := by
      rw [holomorphicLineSectionIntegralPair_smul_right]
    _ = _ := by rw [map_mul, holomorphicLineSectionIntegralPair_conj]

@[instance_reducible]
def holomorphicLineSectionInnerProductCore : InnerProductSpace.Core ℂ (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) where
  inner := IntegralPair.holomorphicLineSectionIntegralPair V u
  conj_inner_symm s t := holomorphicLineSectionIntegralPair_conj V u t s
  re_inner_nonneg := IntegralPair.holomorphicLineSectionIntegralPair_nonneg V u
  add_left := holomorphicLineSectionIntegralPair_add_left V u
  smul_left s t z := holomorphicLineSectionIntegralPair_smul_left V u s t z
  definite s hs := IntegralPair.holomorphicLineSectionIntegralPair_definite V u s (congrArg Complex.re hs)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.InnerProduct
