import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedParameterRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedParameter
import OAI.ArithmeticGeometry.Descent.CMVariety.GroupLevelComparisons
import OAI.ArithmeticGeometry.Descent.CMVariety.CountableModuliImages
import OAI.ArithmeticGeometry.Descent.CMVariety.NumberFieldBaseContinuity

/-! # Moduli -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
CM descent for the saved arithmetic moduli interface. The enhancement,
arithmetic parameter, analytic group/level rigidity, countable polarization
image, and open-chart isolation are all supplied by proved constructions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter Set
open scoped _root_.Topology

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.moduli_point_descends_of_retained_rigidity
    (M : StandardModuli.Abelian.ArithmeticAbelianModuli) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space) {m : ℕ}
    {k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (M.universal.pullback p).polarized.abelian}
    (D : EnhancedChart.Abelian.SmoothEnhancedParameter M.rationalStructureMap M.universal p k)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation (M.universal.pullback p).polarized.abelian)
    (h : ∀ᶠ s in 𝓝 D.nativeCenter,
      ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso D.nativeFamily.polarized.abelian
        D.nativeFamily.polarized.level D.nativeFamily.endomorphism D.nativeCenter s) :
    ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ M.space,
      Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p := by
  have hb : ∀ᶠ s in 𝓝 D.nativeCenter,
      D.nativePointMap s ≫ M.parameter.hom = p ≫ M.parameter.hom := by
    have hb₀ : ∀ᶠ s in 𝓝 D.nativeCenter,
        D.nativePointMap s ≫ M.parameter.hom = D.nativePointMap D.nativeCenter ≫ M.parameter.hom := by
      simpa only [EnhancedChart.Abelian.SmoothEnhancedParameter.nativePointMap, Category.assoc] using
        NumberFieldBaseContinuity.Abelian.numberField_structure_locally_constant
          (D.nativeProjection ≫ D.map ≫ M.parameter.hom) D.nativeCenter
    simpa only [D.nativeCenter_original] using hb₀
  let U := {s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase |
    ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso D.nativeFamily.polarized.abelian
      D.nativeFamily.polarized.level D.nativeFamily.endomorphism D.nativeCenter s ∧
      D.nativePointMap s ≫ M.parameter.hom = p ≫ M.parameter.hom}
  have hU : U ∈ 𝓝 D.nativeCenter := h.and hb
  let A₀ := D.nativeFamily.pullback D.nativeCenter.left
  let e (s : U) : UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso A₀ (M.universal.pullback (D.nativePointMap s.val)) :=
    (Classical.choice (GroupLevelComparisons.Abelian.FamilyPoints.unpolarized_comparison_of_actual_fiber_iso
      D.nativeFamily D.nativeCenter s.val s.property.1)).trans
        (UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso.ofEnhanced (D.nativeFiberIso s.val))
  have hc := M.countable_image_of_unpolarized_comparisons
    (fun s : U => D.nativePointMap s.val) A₀ (D.nativeCenterPresentation P) e
    (fun s t => s.property.2.trans t.property.2.symm)
  apply D.numberField_of_countable_point_map_image hU
  apply hc.mono
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩

theorem Moduli.Abelian.cm_moduli_point_is_algebraic (M : StandardModuli.Abelian.StandardAbelianModuli)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space) (hCM : (M.abelianAt p).HasCMH1) :
    M.IsAlgebraicPoint p := by
  let M₀ := M.toArithmeticAbelianModuli
  obtain ⟨_, D, hD⟩ := EnhancedParameterRigidity.Abelian.cm_point_has_smooth_locally_rigid_enhanced_parameter
    M₀.rationalStructureMap M₀.universal p M.complexFiber (M.complexFiber p) hCM
    (show 0 < M.level from lt_of_lt_of_le (by decide : 0 < 3) M.deepLevel)
  exact D.moduli_point_descends_of_retained_rigidity M₀ p (M.complexFiber p) hD

end

end OAI.ArithmeticGeometry.Descent.CMVariety
