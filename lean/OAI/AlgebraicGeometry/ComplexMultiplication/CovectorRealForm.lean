import OAI.Analysis.DifferentialForms.Manifold.CovectorAction

/-! # Covector Real Form -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CovectorRealForm

noncomputable section

/-! # Complex covector fields on actual real tangent spaces

Restriction of scalars and the genuine preferred tangent equivalence give a
faithful map to real tangent forms. These forms have actual type `(p,0)`.
Smoothness and closedness remain separate properties of a field.
-/

open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- A complex covector field, expressed through the actual real tangent-coordinate equivalence. -/
def complexCovectorFieldToRealForm (p : ℕ)
    (field : M → E [⋀^Fin p]→L[ℂ] ℂ) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M p :=
  fun x => ((field x).restrictScalars ℝ).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).toContinuousLinearMap

/-- The actual tangent transport loses no covector values. -/
theorem complexCovectorFieldToRealForm_injective (p : ℕ) :
    Function.Injective (complexCovectorFieldToRealForm (E := E) (M := M) p) := by
  intro a b h
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  let e := Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x
  have hv := congrArg (fun g : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M p =>
    g x (fun i => e.symm (v i))) h
  change a x (fun i => e (e.symm (v i))) = b x (fun i => e (e.symm (v i))) at hv
  simpa only [e.apply_symm_apply] using hv

/-- Complex multilinearity gives the original inverse character on actual real tangents. -/
theorem complexCovectorFieldToRealForm_hasTangentBidegree (p : ℕ)
    (field : M → E [⋀^Fin p]→L[ℂ] ℂ) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M p 0 (complexCovectorFieldToRealForm p field) := by
  intro x z v
  let e := Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x
  change field x (fun i => e (e.symm ((↑(z⁻¹) : ℂ) • e (v i)))) =
    (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ 0)⁻¹) * field x (fun i => e (v i))
  simp only [e.apply_symm_apply]
  have h := (field x).toAlternatingMap.map_smul_univ
    (fun _ : Fin p => (↑(z⁻¹) : ℂ)) (fun i => e (v i))
  simpa using h

/-- Therefore the field has genuine pure bidegree in every chart of the actual atlas. -/
theorem complexCovectorFieldToRealForm_hasManifoldBidegree (p : ℕ)
    (field : M → E [⋀^Fin p]→L[ℂ] ℂ) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p 0 (complexCovectorFieldToRealForm p field) :=
  (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr
    (complexCovectorFieldToRealForm_hasTangentBidegree p field)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CovectorRealForm
