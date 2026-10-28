import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionValues
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.OpenDifferentiableLift

/-! # Open Regular Function Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionHolomorphic

noncomputable section

/-! Local holomorphy of actual regular-section values on a native open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

set_option backward.isDefEq.respectTransparency false in
theorem openRegularFunctionValue_comp_differentiableAt
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (U : X.left.Opens) (s : Γ(X.left, U)) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (x : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p x)
    (hx : (p x).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) :
    DifferentiableAt ℂ (OpenRegularFunctionValues.openRegularFunctionValue X U s ∘ p) x := by
  let Y := OpenRegularFunctionValues.regularOpenScheme X U
  let f := OpenRegularFunctionValues.regularOpenInclusion X U
  have hrange : p x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion f]
    exact ⟨⟨(p x).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase), hx⟩, rfl⟩
  obtain ⟨q, hq⟩ := hrange
  let : Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := ⟨q⟩
  let : Nonempty Y.left := ⟨q.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  let : IsIntegral Y.left := isIntegral_of_isOpenImmersion f.left
  let : Smooth Y.hom := inferInstanceAs (Smooth (U.ι ≫ X.hom))
  let h := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f
  let e := h.toOpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  let g := e.symm ∘ p
  have hg := Intrinsic.OpenDifferentiableLift.mdifferentiableAt_nativeOpenInverse f p x hp ⟨q, hq⟩
  have hdiff := ((OpenRegularFunctionValues.regularFunctionValue_contMDiff Y (U.topIso.inv s) 1).mdifferentiableAt
    one_ne_zero).comp x hg
  apply hdiff.differentiableAt.congr_of_eventuallyEq
  have htarget : e.target = Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
    h.toOpenPartialHomeomorph_target _
  filter_upwards [hp.continuousAt (e.open_target.mem_nhds (htarget.symm ▸ ⟨q, hq⟩))] with y hy
  have heq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (g y) = p y :=
    h.toOpenPartialHomeomorph_right_inv _ (htarget ▸ hy)
  exact (congrArg (OpenRegularFunctionValues.openRegularFunctionValue X U s) heq).symm.trans
    (OpenRegularFunctionValues.openRegularFunctionValue_inclusion X U s (g y))

end

end OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionHolomorphic
