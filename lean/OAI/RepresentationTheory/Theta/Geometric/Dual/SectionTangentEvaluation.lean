import OAI.RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent

/-! # Section Tangent Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.SectionTangentEvaluation

noncomputable section

/-! Native dual-number section values recover the actual complex
manifold derivative, first on an affine test and then on the scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

theorem affineDualSectionValue_snd (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤))
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (v : TangentSpace (𝓘(ℂ, Fin (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) x) :
    (SectionEvaluation.dualGlobalSectionValue ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualOpen.affineDualSchemeMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x v).val) ≫ i).left s).snd =
      mfderiv (𝓘(ℂ, Fin (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) (𝓘(ℂ, ℂ))
        (RegularFunctionContinuity.regularFunctionValue X s ∘ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x v := by
  have heq : RegularFunctionContinuity.regularFunctionValue X s ∘ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i =
      fun y => y ((Scheme.ΓSpecIso (.of A)).hom (i.left.appTop s)) :=
    funext (RegularFunctionContinuity.regularFunctionValue_affineTest X s A i)
  rw [heq]
  have H := SectionEvaluation.dualGlobalSectionValue_pullback
    (Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x v).val.toRingHom)) i.left s
  have H' := SectionEvaluation.dualGlobalSectionValue_spec (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x v).val.toRingHom (i.left.appTop s)
  exact (congrArg TrivSqZeroExt.snd (H.trans H')).trans
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPoint_snd x v ((Scheme.ΓSpecIso (.of A)).hom (i.left.appTop s)))

theorem nativeDualSectionValue_snd (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (s : Γ(X.left, ⊤)) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (v : TangentSpace (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p) :
    (SectionEvaluation.dualGlobalSectionValue (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val.left s).snd =
      mfderiv (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) (𝓘(ℂ, ℂ))
        (RegularFunctionContinuity.regularFunctionValue X s) p v := by
  obtain ⟨U, hU, x, hx⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X p
  have hpU : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U := by
    have H : p ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨x, hx⟩
    rwa [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at H
  let : Nonempty U := ⟨⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, hpU⟩⟩
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let : IsDomain A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U
  let : Algebra.Smooth ℂ A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  have hx' : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x = p := hx
  obtain ⟨w, hw⟩ := (AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A i x).surjective v
  subst p
  rw [← hw]
  have hdual := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDual_mfderiv X A i x w
  have H := congrArg (fun q => (SectionEvaluation.dualGlobalSectionValue (Over.Hom.left q) s).snd) hdual
  have hc := mfderiv_comp_apply x
    ((OpenRegularFunctionValues.regularFunctionValue_contMDiff X s 1).mdifferentiableAt one_ne_zero)
    ((AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap A i 1).mdifferentiableAt one_ne_zero) w
  exact H.trans ((affineDualSectionValue_snd X s A i x w).trans hc)

theorem nativeDualSectionValue_periodDerivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (s : Γ(X.left, ⊤)) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z a : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z) :
    (SectionEvaluation.dualGlobalSectionValue (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X (p z)
      (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z a)).val.left s).snd =
      fderiv ℂ (RegularFunctionContinuity.regularFunctionValue X s ∘ p) z a := by
  have H := nativeDualSectionValue_snd X s (p z)
    (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z a)
  have hc := mfderiv_comp_apply z
    ((OpenRegularFunctionValues.regularFunctionValue_contMDiff X s 1).mdifferentiableAt one_ne_zero) hp a
  exact H.trans (hc.symm.trans (congrArg (fun f : V →L[ℂ] ℂ => f a)
    (mfderiv_eq_fderiv (𝕜 := ℂ) (f := RegularFunctionContinuity.regularFunctionValue X s ∘ p) (x := z))))

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.SectionTangentEvaluation
