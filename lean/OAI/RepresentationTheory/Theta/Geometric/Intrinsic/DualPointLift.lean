import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality

/-! # Dual Point Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift

noncomputable section

/-! Surjectivity of the actual differential lifts every native
dual-number point with the prescribed reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

theorem exists_nativeDualPoint_lift {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hf : Function.Surjective (mfderiv
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) p))
    (q : AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) :
    ∃ r : AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints X p, r.val ≫ f = q.val := by
  obtain ⟨v, hv⟩ := hf ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).symm q)
  refine ⟨AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v, ?_⟩
  have H := AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality.nativeSchemeTangentDual_natural f p v
  have H' := congrArg (fun w => (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) w).val) hv
  exact H.symm.trans (H'.trans
    (congrArg Subtype.val ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).apply_symm_apply q)))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift
