import OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative

/-! # Projective Irreducibility Of -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveIrreducibilityOf.Constructions.ProjectiveIrreducibility

noncomputable section

/-!
# RiemannProjectivity: irreducibility of the genuine projective closure

In a standard affine chart, a Zariski closed subset is a common polynomial
zero locus. Its pullback under the holomorphic universal-cover map has local
holomorphic equations. Analytic continuation proves that the image, and
hence its Zariski closure, is irreducible.
-/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Topology

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

theorem closed_preimage_local_equations
    (f : V → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ x, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x) ∧
      DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x)
    (Z : Set (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (hZ : IsClosed Z) (x : V) :
    AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.HasLocalEquations ((ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint ∘ f) ⁻¹' Z) x := by
  classical
  obtain ⟨i, hi, _⟩ := hd x
  let U : Set V := {y | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f y)}
  let r : V → ({j : Fin (n + 1) // j ≠ i} → ℂ) :=
    fun y j => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y) j.val
  have hU : IsOpen U := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage hf
  have hr : DifferentiableOn ℂ r U := by
    intro y hy
    apply differentiableWithinAt_pi.mpr
    intro j
    exact differentiableWithinAt_pi.mp (RiemannProjectivity.Fin.Constructions.coordinates_differentiableOn_patch f hf hd i y hy) j.val
  let Z' : Set (PrimeSpectrum (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)) :=
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i) ⁻¹' Z
  have hZ' : IsClosed Z' := hZ.preimage (AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i).continuous
  obtain ⟨S, hS⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z').mp hZ'
  let F : Set (V → ℂ) := range (fun p : S => fun y => MvPolynomial.eval (r y) p.val)
  refine ⟨U, hU, hi, F, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact (AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval p.val).comp_differentiableOn hr
  · intro y hy
    have hpoint := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_on_patch n i ⟨f y, hy⟩
    change (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f y)).left (IsLocalRing.closedPoint ℂ) ∈ Z ↔ _
    rw [hpoint, AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveAffineSchemePoint_left]
    change PrimeSpectrum.comap (MvPolynomial.eval (r y)) (IsLocalRing.closedPoint ℂ) ∈ Z' ↔ _
    rw [hS]
    change (∀ p ∈ S, MvPolynomial.eval (r y) p ∈ IsLocalRing.maximalIdeal ℂ) ↔ _
    simp only [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    constructor
    · rintro h _ ⟨p, rfl⟩
      exact h p.val p.property
    · intro h p hp
      exact h _ ⟨⟨p, hp⟩, rfl⟩

theorem irreducible_underlying_image
    (f : V → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ x, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x) ∧
      DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) :
    IsIrreducible (ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint '' range f) := by
  rw [← range_comp]
  exact AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.isIrreducible_range (ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint ∘ f) (closed_preimage_local_equations f hf hd)

theorem irreducible_closure_support
    (f : V → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ x, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x) ∧
      DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) :
    IsIrreducible (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureSupport (range f) : Set (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) :=
  (irreducible_underlying_image f hf hd).closure

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem closureScheme_integral_of_irreducible
    (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (hS : IsIrreducible (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureSupport S : Set (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))) :
    IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme S) := by
  have hr : IsIrreducible (range (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S)) := by
    rwa [ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusion_range]
  let : IrreducibleSpace (range (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S)) := Subtype.irreducibleSpace hr
  let : IrreducibleSpace (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme S) :=
    (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S).isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
      inferInstance
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

theorem closureScheme_integral_of_holomorphic
    (f : V → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ x, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x) ∧
      DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) :
    IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) :=
  closureScheme_integral_of_irreducible _ (irreducible_closure_support f hf hd)

/-- Taking the image of a holomorphic universal cover gives an actual
integral projective closure of the embedded torus. -/
theorem closureScheme_integral_of_torus_embedding
    (Λ : AddSubgroup V) (f : V ⧸ Λ → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Continuous f)
    (hd : ∀ z : V, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z) :
    IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) := by
  have hrange : range (fun z : V => f (QuotientAddGroup.mk z)) = range f := by
    change range (f ∘ QuotientAddGroup.mk) = range f
    rw [range_comp, QuotientAddGroup.mk_surjective.range_eq, image_univ]
  have h := closureScheme_integral_of_holomorphic
    (fun z : V => f (QuotientAddGroup.mk z))
    (hf.comp QuotientAddGroup.continuous_mk) hd
  rwa [hrange] at h

theorem integral_projective_period_closure
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧ IsIntegral (ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) ∧
      Topology.IsClosedEmbedding (ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap f) := by
  obtain ⟨n, f, hf, hd⟩ := RiemannProjectivity.Fin.Constructions.projective_period_torus hRiemannProjectivity Φ
  refine ⟨n, f, hf, closureScheme_integral_of_torus_embedding _ f hf.continuous ?_,
    ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_isClosedEmbedding f hf⟩
  intro z
  obtain ⟨i, hi, hdi, _⟩ := hd z
  exact ⟨i, hi, hdi⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveIrreducibilityOf.Constructions.ProjectiveIrreducibility
