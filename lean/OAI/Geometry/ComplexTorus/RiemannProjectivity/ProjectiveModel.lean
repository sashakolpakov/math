import OAI.Geometry.ComplexTorus.RiemannProjectivity.ExactProjective
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveIrreducibilityOf

/-! # Projective Model -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveModel.Constructions.ProjectiveTorusModel

noncomputable section

/-! # RiemannProjectivity: an integral projective scheme with exactly the period torus as complex points -/

open Set Filter _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Topology
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

theorem coordinates_differentiableAt {f : V → Projectivization ℂ (Fin (n + 1) → ℂ)}
    {x : V} (hf : ContinuousAt f x) (i : Fin (n + 1)) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x))
    (hd : DifferentiableAt ℂ (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) x) :
    DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x := by
  have hpair : DifferentiableAt ℂ (fun y => ((1 : ℂ), AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y))) x :=
    (differentiableAt_const 1).prodMk hd
  have hG := (ConeTangentF.Constructions.ConeTangent.insertCoordinate i).differentiableAt.comp x hpair
  apply hG.congr_of_eventuallyEq
  filter_upwards [hf.preimage_mem_nhds ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).mem_nhds hi)] with y hy
  change AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y) = i.insertNth 1 (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y))
  ext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa only [Fin.insertNth_apply_same] using AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates_self i (f y) hy
  · simp only [Fin.insertNth_apply_succAbove]
    rfl

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem exists_integral_projective_model (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f))),
      Topology.IsClosedEmbedding f ∧ IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) ∧
      (∀ t, e t = ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap f t) ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)) (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t) := by
  obtain ⟨n, f, Q, hf, hd, hQ, hcone⟩ :=
    AlgebraicPeriod.Constructions.AlgebraicPeriodCone.period_cone_homogeneous_equations hRiemannProjectivity Φ
  have hsurj := ExactProjective.Constructions.ExactProjectiveClosure.liftedMap_surjective f Q hQ hcone
  let e := (ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_isClosedEmbedding f hf).isEmbedding.toHomeomorphOfSurjective hsurj
  have hint : IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) :=
    ProjectiveIrreducibilityOf.Constructions.ProjectiveIrreducibility.closureScheme_integral_of_torus_embedding _ f hf.continuous (by
      intro z
      obtain ⟨i, hi⟩ := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (f (QuotientAddGroup.mk z))
      exact ⟨i, hi, coordinates_differentiableAt
        (hf.continuous.comp QuotientAddGroup.continuous_mk).continuousAt i hi (hd z i hi).1⟩)
  exact ⟨n, f, e, hf, hint, fun _ => rfl, ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_inclusion f⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveModel.Constructions.ProjectiveTorusModel
