import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Matching -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching.CM

noncomputable section

/-! Uniqueness of the actual theta form from its pullback to the ball.
Surjectivity of the covering map and of its derivative detect one-forms.
The equality is on the actual manifold forms, not a new identification
assumed in the family data. -/

open scoped Classical _root_.Manifold TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

section Derivatives

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W]
  [IsScalarTower ℝ ℂ W]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [TopologicalSpace N] [ChartedSpace W N]

theorem mdifferentiableAt_real {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, W) f x) :
    MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) f x := by
  obtain ⟨hc, hd⟩ := (mdifferentiableAt_iff f x).mp hf
  apply (mdifferentiableAt_iff f x).mpr
  refine ⟨hc, ?_⟩
  have hr := hd.restrictScalars ℝ
  simpa only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id] using hr

theorem real_mfderiv_eq_complex {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, W) f x) :
    (show V →L[ℝ] W from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) f x) =
      (show V →L[ℂ] W from mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) f x).restrictScalars ℝ := by
  let c : V → W := fun z => chartAt W (f x)
    (f ((chartAt V x).symm z))
  have hd : DifferentiableAt ℂ c (chartAt V x x) := by
    simpa only [TangentSpace, c, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, differentiableWithinAt_univ]
      using hf.differentiableWithinAt_writtenInExtChartAt
  have hr : (show V →L[ℝ] W from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) f x) =
      fderiv ℝ c (chartAt V x x) := by
    have he := (mdifferentiableAt_real hf).mfderiv
    simp only [TangentSpace, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, fderivWithin_univ] at he
    convert! he using 1
  have hc : (show V →L[ℂ] W from mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) f x) =
      fderiv ℂ c (chartAt V x x) := by
    have he := hf.mfderiv
    simp only [TangentSpace, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, fderivWithin_univ] at he
    convert! he using 1
  rw [hr, hc]
  exact hd.fderiv_restrictScalars ℝ

end Derivatives

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

theorem forms_eq_of_cover_evaluations
    (B : GeometricSource.CM.BallDatum E) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ)
    (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)
    (α β : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm X.analyticModel X.analyticSpace 1)
    (h : ∀ z ξ, α (π z)
        (fun _ : Fin 1 => mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ) =
      β (π z) (fun _ : Fin 1 =>
        mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ)) : α = β := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  obtain ⟨z, rfl⟩ := hπ.2.1 x
  obtain ⟨ξ, hξ⟩ := (hπ.2.2.2.2.1 z).2 (v 0)
  have heq : mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ = v 0 := by
    exact (congrArg (fun A : GeometricSource.CM.BallChart →L[ℝ] X.analyticModel => A ξ)
      (real_mfderiv_eq_complex (hπ.2.2.2.1 z))).trans hξ
  have hv : v = fun _ : Fin 1 => v 0 := by
    funext i
    exact congrArg v (Subsingleton.elim i 0)
  rw [hv, ← heq]
  exact h z ξ

/-- Any two closed pure forms representing the literal same theta
derivative on the same covering ball are equal. -/
theorem representsTheta_unique
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : B.IsBallCover N X π)
    (α β : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hα : GeometricSource.CM.RepresentsTheta E L φ X π α) (hβ : GeometricSource.CM.RepresentsTheta E L φ X π β) : α = β := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact forms_eq_of_cover_evaluations E B X N π hπ α.val.val.val β.val.val.val
    (fun z ξ => (hα z ξ).trans (hβ z ξ).symm)

/-- Equality of actual theta representatives also identifies their classes
in the original rational complexification, using the canonical coefficient map. -/
theorem theta_classes_match
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) [FiniteDimensional ℚ (X.rationalCohomology 1)]
    (N : ℕ) (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)
    (α β : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hα : GeometricSource.CM.RepresentsTheta E L φ X π α) (hβ : GeometricSource.CM.RepresentsTheta E L φ X π β)
    (a b : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (ha : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 a =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 α.val))
    (hb : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 b =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 β.val)) : a = b := by
  apply ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace X.toOver) 1
  rw [ha, hb, representsTheta_unique E L φ X N π hπ α β hα hβ]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching.CM
