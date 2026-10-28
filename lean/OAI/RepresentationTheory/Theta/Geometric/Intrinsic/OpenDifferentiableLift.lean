import OAI.RepresentationTheory.Theta.Geometric.DifferentiableLocalLift
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Open Differentiable Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.OpenDifferentiableLift

noncomputable section

section

/-! Differentiable lifting through an actual open immersion of smooth
integral complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

set_option backward.isDefEq.respectTransparency false in
theorem mdifferentiableAt_nativeOpenLift (f : X ⟶ Y) [IsOpenImmersion f.left]
    (g : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (x : V) (hg : ContinuousAt g x)
    (hfg : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ g) x) :
    MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) g x := by
  let d : (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) →L[ℂ]
      (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) :=
    mfderiv (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (g x)
  have hd := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective f (g x)
  obtain ⟨i, hi⟩ := DifferentiableLocalLift.continuousLinearMap_exists_leftInverse d hd
  exact DifferentiableLocalLift.mdifferentiableAt_localLift (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) g x d i
    (((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f 1).mdifferentiableAt one_ne_zero).hasMFDerivAt)
    hi hg hfg

end

/-! Holomorphic local inverse functions for native open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

theorem mdifferentiableAt_nativeOpenInverse (f : X ⟶ Y) [IsOpenImmersion f.left]
    [Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (x : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)) p x)
    (hx : p x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) :
    MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f).toOpenPartialHomeomorph
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)).symm ∘ p) x := by
  let h := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f
  let e := h.toOpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  have htarget : e.target = Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
    h.toOpenPartialHomeomorph_target _
  have hg : ContinuousAt (e.symm ∘ p) x :=
    (e.continuousAt_symm (htarget.symm ▸ hx)).comp hp.continuousAt
  have heq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ (e.symm ∘ p) =ᶠ[𝓝 x] p := by
    filter_upwards [hp.continuousAt (e.open_target.mem_nhds (htarget.symm ▸ hx))] with y hy
    exact h.toOpenPartialHomeomorph_right_inv _ (htarget ▸ hy)
  exact mdifferentiableAt_nativeOpenLift f (e.symm ∘ p) x hg
    (hp.congr_of_eventuallyEq heq)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.OpenDifferentiableLift
