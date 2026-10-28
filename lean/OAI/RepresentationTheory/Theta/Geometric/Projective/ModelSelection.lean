import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ManifoldSelection
import OAI.RepresentationTheory.Theta.Geometric.Projective.IntrinsicEmbedding

/-! # Model Selection -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.ModelSelection

noncomputable section

/-! Countable holomorphic selection for actual algebraic target maps,
by a single fixed projective embedding of the original target scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [BaireSpace E]

theorem projective_model_countable_selection
    (U : TopologicalSpace.Opens E) [Nonempty U] (hc : IsPreconnected (U : Set E))
    {Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Z.left Z.hom)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : X.toOver ⟶ Z) (f : U → X.analyticSpace)
    (hf : ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, X.analyticModel)) 1 f)
    {I : Type*} [Countable I] (Y : I → AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : ∀ i, (Y i).toOver ⟶ Z) (g : ∀ i, U → (Y i).analyticSpace)
    (hg : ∀ i, ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, (Y i).analyticModel)) 1 (g i))
    (hcover : ∀ x, ∃ i, f x ≫ a = g i x ≫ b i) :
    ∃ i, ∀ x, f x ≫ a = g i x ≫ b i := by
  let V : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension)
  let : IsIntegral V.left := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.isIntegral_projectiveSpace P.ambientDimension
  let : Smooth V.hom := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.smooth_projectiveSpaceToBase P.ambientDimension
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let e : Z ⟶ V := P.toOverHom
  let : IsClosedImmersion e.left := P.closedImmersion
  let : Mono e := Over.mono_of_mono_left e
  let F : U → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V := fun x => f x ≫ a ≫ e
  let G : I → U → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V := fun i x => g i x ≫ b i ≫ e
  have hF : ContMDiff (𝓘(ℂ, E))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.hom) → ℂ)) 1 F :=
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (a ≫ e) 1).comp hf
  have hG (i : I) : ContMDiff (𝓘(ℂ, E))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.hom) → ℂ)) 1 (G i) := by
    let : IsIntegral (Y i).toOver.left := (Y i).property
    let : Smooth (Y i).toOver.hom := (Y i).presentation.smooth
    exact (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (b i ≫ e) 1).comp (hg i)
  obtain ⟨i, hi⟩ := Holomorphic.ManifoldSelection.open_holomorphic_countable_selection U hc F G hF hG (fun x => by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, congrArg (fun z => z ≫ e) hi⟩)
  refine ⟨i, fun x => (cancel_mono e).mp ?_⟩
  exact congrFun hi x

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.ModelSelection
