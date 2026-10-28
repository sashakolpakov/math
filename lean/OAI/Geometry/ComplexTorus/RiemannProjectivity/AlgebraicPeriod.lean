import OAI.Geometry.ComplexTorus.RiemannProjectivity.SeparatingLinearCoordinates
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation
import OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialSeparationFinite

/-! # Algebraic Period -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.AlgebraicPeriod.Constructions.AlgebraicPeriodCone

noncomputable section

/-! # RiemannProjectivity: the actual CM period cone is cut out by homogeneous polynomials -/

open Set

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {n : ℕ}

theorem separating_polynomial (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ))
    (hker : ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0)
    (hsurj : Function.Surjective (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v))
    (v : Fin (n + 1) → ℂ) (hv : v ∉ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) :
    ∃ p : MvPolynomial (Fin (n + 1)) ℂ,
      (∀ w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), MvPolynomial.eval w p = 0) ∧ MvPolynomial.eval v p ≠ 0 := by
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hp := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hclosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) L hker
  have hfinite := FiniteCone.Constructions.FiniteConeFibers.finite_proper_cone_fiber L hp hker
    (FiniteCone.Constructions.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd)
  obtain ⟨l, hl, hsep⟩ := SeparatingLinearCoordinates.Constructions.LinearSeparation.exists_coordinate L hsurj hfinite hv
  obtain ⟨_, F, _, _, _, heq⟩ :=
    GlobalEquation.Constructions.PeriodAlgebraicCoordinates.coordinate_equation Φ f hf hd L hker hsurj l hl
  refine ⟨GlobalEquation.Constructions.LinearPolynomial.pullback L l F, ?_, ?_⟩
  · intro w hw
    rw [GlobalEquation.Constructions.LinearPolynomial.eval_pullback]
    exact (heq (L w) (l w)).mp ⟨w, hw, rfl⟩
  · intro hz
    rw [GlobalEquation.Constructions.LinearPolynomial.eval_pullback] at hz
    obtain ⟨w, hw, he⟩ := (heq (L v) (l v)).mpr hz
    exact hsep w hw (congrArg Prod.fst he) (congrArg Prod.snd he)

theorem period_cone_homogeneous_equations (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      (∀ q ∈ Q, ∃ k, q.IsHomogeneous k) ∧
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} := by
  obtain ⟨n, f, L, hf, hd, hker, _, hi⟩ :=
    RegularConeOf.Constructions.RegularCone.proper_period_cone_projection_with_interior_and_immersions hRiemannProjectivity Φ
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hsurj := ConeSurjectivityEq.Constructions.ConeSurjectivity.surjective_cone_projection L hclosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _)
    hker (FiniteCone.Constructions.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd) hi
  obtain ⟨Q, hQ, heq⟩ := PolynomialSeparationFinite.Constructions.PolynomialSeparation.homogeneous_equations (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _)
    (separating_polynomial Φ f hf hd L hker hsurj)
  exact ⟨n, f, Q, hf, hd, hQ, heq⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.AlgebraicPeriod.Constructions.AlgebraicPeriodCone
