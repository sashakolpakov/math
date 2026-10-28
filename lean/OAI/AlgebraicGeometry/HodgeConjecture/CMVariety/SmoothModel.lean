import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicSmoothChartEmbedding
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicProjectiveIrreducibility
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartIff
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicProjectiveTorusModel

/-! # Smooth Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.SmoothModel.CM.Abelian.Algebraization.SmoothProjectiveTorusModel

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {n : ℕ}

theorem smooth_closure
    {S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))}
    (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)) (hQ : ∀ q ∈ Q, ∃ d, q.IsHomogeneous d)
    (hS : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0})
    (hsm : ∀ i : Fin (n + 1), Algebra.Smooth ℂ
      (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S) i))) :
    Smooth (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver S).hom := by
  apply Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureChartCover.smooth S
  intro i
  exact Geometry.ComplexTorus.RiemannProjectivity.AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra.smooth_of_polynomial_point_image (Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureAffineChart.over S i)
    (Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureAffineChart.embedding S i) _ (Geometry.ComplexTorus.RiemannProjectivity.ClosureChartIff.Constructions.ClosureChartPoints.coordinate_range Q hQ hS i) (hsm i)

def presentation (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (h : Smooth (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver S).hom) : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme S
  structureMap := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureStructureMap S
  projective := Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closurePresentation S
  smooth := h

theorem exists_smooth_integral_projective_model (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (e : Φ.periodTorus ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f))),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : Φ.space) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      IsIntegral (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) ∧ Smooth (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f)).hom ∧
      (∀ t, e t = Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap f t) ∧
      ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)) (e t) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t) := by
  obtain ⟨n, f, Q, hf, hd, hQ, hcone, hsm⟩ := AlgebraicSmoothChartEmbedding.CM.Abelian.Algebraization.SmoothChartEmbedding.exists_embedding Φ
  have hsurj := Geometry.ComplexTorus.RiemannProjectivity.ExactProjective.Constructions.ExactProjectiveClosure.liftedMap_surjective f Q hQ hcone
  let e := (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_isClosedEmbedding f hf).isEmbedding.toHomeomorphOfSurjective hsurj
  have hint : IsIntegral (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) :=
    AlgebraicProjectiveIrreducibility.CM.Abelian.Algebraization.ProjectiveIrreducibility.closureScheme_integral_of_torus_embedding _ f hf.continuous (by
      intro z
      obtain ⟨i, hi⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (f (QuotientAddGroup.mk z))
      exact ⟨i, hi, AlgebraicProjectiveTorusModel.CM.Abelian.Algebraization.ProjectiveTorusModel.coordinates_differentiableAt
        (hf.continuous.comp QuotientAddGroup.continuous_mk).continuousAt i hi (hd z i hi).1⟩)
  exact ⟨n, f, e, hf, hd, hint, smooth_closure Q hQ hcone hsm, fun _ => rfl, Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_inclusion f⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.SmoothModel.CM.Abelian.Algebraization.SmoothProjectiveTorusModel
