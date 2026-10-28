import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularValues
import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionHolomorphic

/-! # Open Regular Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularHolomorphic

noncomputable section

/-! Every actual regular coefficient on an open of the dual-number base
change is locally holomorphic in both coefficients along the original
native period map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Manifold _root_.Topology

set_option backward.isDefEq.respectTransparency false in
theorem dualOpenRegularFunctionValue_differentiableAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (U : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (s : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (x : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p x)
    (hx : (BaseChangeReduction.dualBaseChangeReduction X).left ((p x).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ U) :
    CoefficientHolomorphic.DualCoefficientDifferentiableAt (OpenRegularValues.dualOpenRegularFunctionValue X U s ∘ p) x := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show (p x).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ (BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U from hx)
  let Y := OpenRegularFunctionValues.regularOpenScheme X W
  let f := OpenRegularFunctionValues.regularOpenInclusion X W
  have hrange : p x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion f]
    exact ⟨⟨(p x).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase), hxW⟩, rfl⟩
  obtain ⟨q, hq⟩ := hrange
  let : Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := ⟨q⟩
  let : Nonempty Y.left := ⟨q.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  let : IsIntegral Y.left := isIntegral_of_isOpenImmersion f.left
  let : Smooth Y.hom := inferInstanceAs (Smooth (W.ι ≫ X.hom))
  let : IsAffine Y.left := hW
  have hf : (⊤ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens) ≤
      (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U := by
    apply BaseChangeReduction.dualBaseChange_range_open f U
    rintro _ ⟨t, rfl⟩
    exact hWU t.property
  let sY : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ Y).left, ⊤) :=
    (𝟙 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.appLE U ⊤ hf s
  let h := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f
  let e := h.toOpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  let g := e.symm ∘ p
  have hg := Intrinsic.OpenDifferentiableLift.mdifferentiableAt_nativeOpenInverse f p x hp ⟨q, hq⟩
  have hd := AffineBaseChangeChart.dualConstantPoint_sectionValue_differentiableAt Y g x hg sY
  have heq : OpenRegularValues.dualOpenRegularFunctionValue X U s ∘ p =ᶠ[𝓝 x]
      fun y => SectionEvaluation.dualGlobalSectionValue (AffineBaseChangeChart.dualConstantPoint Y (g y)).left sY := by
    have htarget : e.target = Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
      h.toOpenPartialHomeomorph_target _
    filter_upwards [hp.continuousAt (e.open_target.mem_nhds (htarget.symm ▸ ⟨q, hq⟩))] with y hy
    have he : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (g y) = p y :=
      h.toOpenPartialHomeomorph_right_inv _ (htarget ▸ hy)
    exact (congrArg (OpenRegularValues.dualOpenRegularFunctionValue X U s) he).symm.trans
      (OpenRegularValues.dualOpenRegularFunctionValue_pullback f U s hf (g y))
  constructor
  · apply hd.1.congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg TrivSqZeroExt.fst hy
  · apply hd.2.congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg TrivSqZeroExt.snd hy

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularHolomorphic
