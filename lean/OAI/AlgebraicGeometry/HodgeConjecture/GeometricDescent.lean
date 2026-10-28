import OAI.AlgebraicGeometry.HodgeConjecture.GeometricCoefficients
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe
import Mathlib.RingTheory.Flat.Equalizer

/-! # Geometric Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricDescent.LefschetzNormalization.Geometry

noncomputable section

/-! Faithful comparison of geometric algebraicity over E and over C,
and scalar-conjugation invariance for the actual geometric cycle image. -/

open scoped TensorProduct

theorem range_baseChange (K U V : Type*) [Field K] [Algebra ℚ K]
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (f : U →ₗ[ℚ] V) :
    LinearMap.range (f.baseChange K) = (LinearMap.range f).baseChange K := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul a x => exact Submodule.tmul_mem_baseChange_of_mem a ⟨x, rfl⟩
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul a x =>
      obtain ⟨u, hu⟩ := x.property
      refine ⟨a ⊗ₜ[ℚ] u, ?_⟩
      change a ⊗ₜ[ℚ] f u = a ⊗ₜ[ℚ] (x : V)
      rw [hu]

theorem quotient_baseChange_kernel (K V : Type*) [Field K] [Algebra ℚ K]
    [AddCommGroup V] [Module ℚ V] (P : Submodule ℚ V) :
    LinearMap.ker (P.mkQ.baseChange K) = P.baseChange K := by
  change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor K K P.mkQ) = _
  rw [Module.Flat.ker_lTensor_eq, Submodule.ker_mkQ]
  rfl

theorem coefficientInclusion_injective (E : IntermediateField ℚ ℂ)
    (V : Type*) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E V) :=
  TensorProduct.map_injective_of_flat_flat E.val.toLinearMap LinearMap.id
    (fun _ _ h => Subtype.ext h) Function.injective_id

/-- Extending the coefficient field from E to C reflects membership in
every rational subspace, in particular the geometric cycle-class image. -/
theorem inclusion_mem_baseChange_iff (E : IntermediateField ℚ ℂ)
    (V : Type*) [AddCommGroup V] [Module ℚ V] (P : Submodule ℚ V)
    (x : E ⊗[ℚ] V) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E V x ∈ P.baseChange ℂ ↔ x ∈ P.baseChange E := by
  rw [← quotient_baseChange_kernel ℂ V P, ← quotient_baseChange_kernel E V P,
    LinearMap.mem_ker, LinearMap.mem_ker]
  rw [← ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_baseChange]
  constructor
  · intro h
    exact coefficientInclusion_injective E (V ⧸ P) (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

/-- This identifies the finite E-linear cycle image with its complex
counterpart on the identical variety and identical cohomology class. -/
theorem geometric_realize_iff (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (x : E ⊗[ℚ] X.rationalCohomology (p + p)) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X (p + p) x ∈ X.complexGeometricAlgebraicClasses p ↔
      x ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p := by
  let : Module.Finite ℚ (X.rationalCohomology (p + p)) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X (p + p)
  change _ ↔ x ∈ LinearMap.range ((X.geometricCycleClassMap p).baseChange E)
  rw [range_baseChange]
  change _ ↔ x ∈ (X.geometricAlgebraicClasses p).baseChange E
  rw [← inclusion_mem_baseChange_iff]
  constructor
  · rintro ⟨z, hz, he⟩
    have hzx : z = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E (X.rationalCohomology (p + p)) x :=
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace X.toOver) (p + p) he
    exact hzx ▸ hz
  · intro h
    exact ⟨ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E (X.rationalCohomology (p + p)) x, h, rfl⟩

theorem scalarConjugate_inverse (E : IntermediateField ℚ ℂ)
    (V : Type*) [AddCommGroup V] [Module ℚ V]
    (g : Gal(E/ℚ)) (x : E ⊗[ℚ] V) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E V g⁻¹ (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E V g x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      simp only [ComplexMultiplication.ScalarDescent.CM.scalarConjugate_tmul]
      exact congrArg (fun b : E => b ⊗ₜ[ℚ] x) (g.symm_apply_apply a)

theorem geometric_scalarConjugate_iff (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (g : Gal(E/ℚ))
    (x : E ⊗[ℚ] X.rationalCohomology (p + p)) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology (p + p)) g x ∈
        Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p ↔
      x ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p := by
  constructor
  · intro h
    have hi := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_scalarConjugate E X p g⁻¹ h
    rwa [scalarConjugate_inverse] at hi
  · exact Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_scalarConjugate E X p g

theorem complex_geometric_scalarConjugate_iff (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (g : Gal(E/ℚ))
    (x : E ⊗[ℚ] X.rationalCohomology (p + p)) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X (p + p)
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology (p + p)) g x) ∈
        X.complexGeometricAlgebraicClasses p ↔
      Coefficients.CM.SurfaceConstruction.realizeCoefficient E X (p + p) x ∈ X.complexGeometricAlgebraicClasses p := by
  rw [geometric_realize_iff, geometric_realize_iff, geometric_scalarConjugate_iff]

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricDescent.LefschetzNormalization.Geometry
