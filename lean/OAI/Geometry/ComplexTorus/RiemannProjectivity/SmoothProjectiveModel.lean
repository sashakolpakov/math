import OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartIff
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveModel

/-! # Smooth Projective Model -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothProjectiveModel.Constructions.SmoothProjectiveTorusModel

noncomputable section

/-! # RiemannProjectivity: the CM period torus has a genuine smooth integral projective model -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {n : ℕ}

theorem smooth_closure
    {S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))}
    (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)) (hQ : ∀ q ∈ Q, ∃ d, q.IsHomogeneous d)
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0})
    (hsm : ∀ i : Fin (n + 1), Algebra.Smooth ℂ
      (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S) i))) :
    Smooth (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver S).hom := by
  apply ClosureChartF.Constructions.ClosureChartCover.smooth S
  intro i
  exact AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra.smooth_of_polynomial_point_image (ClosureChartF.Constructions.ClosureAffineChart.over S i)
    (ClosureChartF.Constructions.ClosureAffineChart.embedding S i) _ (ClosureChartIff.Constructions.ClosureChartPoints.coordinate_range Q hQ hS i) (hsm i)

def presentation (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (h : Smooth (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver S).hom) : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme S
  structureMap := ProjectiveClosureIs.Constructions.ProjectiveClosure.closureStructureMap S
  projective := ProjectiveClosureIs.Constructions.ProjectiveClosure.closurePresentation S
  smooth := h

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem exists_smooth_integral_projective_model (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f))),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) ∧ Smooth (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f)).hom ∧
      (∀ t, e t = ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap f t) ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)) (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t) := by
  obtain ⟨n, f, Q, hf, hd, hQ, hcone, hsm⟩ := SmoothChart.Constructions.SmoothChartEmbedding.exists_embedding hRiemannProjectivity Φ
  have hsurj := ExactProjective.Constructions.ExactProjectiveClosure.liftedMap_surjective f Q hQ hcone
  let e := (ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_isClosedEmbedding f hf).isEmbedding.toHomeomorphOfSurjective hsurj
  have hint : IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) :=
    ProjectiveIrreducibilityOf.Constructions.ProjectiveIrreducibility.closureScheme_integral_of_torus_embedding _ f hf.continuous (by
      intro z
      obtain ⟨i, hi⟩ := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (f (QuotientAddGroup.mk z))
      exact ⟨i, hi, ProjectiveModel.Constructions.ProjectiveTorusModel.coordinates_differentiableAt
        (hf.continuous.comp QuotientAddGroup.continuous_mk).continuousAt i hi (hd z i hi).1⟩)
  exact ⟨n, f, e, hf, hd, hint, smooth_closure Q hQ hcone hsm, fun _ => rfl, ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_inclusion f⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothProjectiveModel.Constructions.SmoothProjectiveTorusModel
