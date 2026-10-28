import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PullbackAffineKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealPullbackSections
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismCoordinate

/-! # Ideal Pullback Chart Surjective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.IdealPullbackChartSurjective.BundleCycles

noncomputable section

/-! The canonical ideal pullback map is surjective on affine
charts lying over affine base charts of an actual pullback square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z X' Z' : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : Z' ⟶ X') (f : X' ⟶ X) (g : Z' ⟶ Z) (hp : IsPullback j g f i)

theorem schemeIdealPullback_affineChart_surjective
    (U : X.affineOpens) (V : X'.affineOpens) (hV : V.1 ≤ f ⁻¹ᵁ U.1) :
    Function.Surjective ((LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm).app V.1) := by
  let α := LineBundles.Scheme.IdealPullbackMap.BundleCycles.schemeIdealPullbackMap i j f g hp.w.symm
  let θ := (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear j V.1).comp (LineBundle.MorphismCoordinate.Cycles.moduleSectionLinearMap α V.1)
  have hle : RingHom.ker (j.app V.1).hom ≤ θ.range := by
    rw [Closed.PullbackAffineKernel.BundleCycles.closedPullback_affineChart_kernel i j f g hp U V hV]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    let s := (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso i U.1).inv ⟨r, hr⟩
    let s' := Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule i) U.1 V.1 hV s
    refine ⟨s', ?_⟩
    have h₁ := LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_apply j V.1 (α.app V.1 s')
    have h₂ := LineBundles.Scheme.IdealPullbackSections.BundleCycles.schemeIdealPullbackMap_sectionToOpen_image i j f g hp.w.symm U.1 V.1 hV s
    have h₃ := congrArg (f.appLE U.1 V.1 hV)
      (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso_inv_apply i U.1 ⟨r, hr⟩)
    exact h₁.trans (h₂.trans h₃)
  intro t
  obtain ⟨s, hs⟩ := hle (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_mem j V.1 t)
  exact ⟨s, (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionLinear_injective j V.1) hs⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.IdealPullbackChartSurjective.BundleCycles
