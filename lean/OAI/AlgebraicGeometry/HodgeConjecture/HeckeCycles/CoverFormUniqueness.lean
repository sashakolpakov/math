import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching

/-! # Cover Form Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFormUniqueness.CM

noncomputable section

/-! The geometric properties of the actual ball cover already detect
one-forms; no equality of arithmetic orbit presentations is needed. -/

open scoped Classical _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM

theorem raw (U : TopologicalSpace.Opens GeometricSource.CM.BallChart) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : U → X.analyticSpace) (hπ : ReferenceCover.CM.CoverProperty U X π)
    (α β : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm X.analyticModel X.analyticSpace 1)
    (h : ∀ z ξ, α (π z)
        (fun _ : Fin 1 => mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ) =
      β (π z) (fun _ : Fin 1 => mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ)) : α = β := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  obtain ⟨z, rfl⟩ := hπ.1 x
  obtain ⟨ξ, hξ⟩ := (hπ.2.2.2 z).2 (v 0)
  have he : mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ = v 0 :=
    (congrArg (fun A : GeometricSource.CM.BallChart →L[ℝ] X.analyticModel => A ξ)
      (Theta.Matching.CM.real_mfderiv_eq_complex (hπ.2.2.1 z))).trans hξ
  have hv : v = fun _ : Fin 1 => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv, ← he]
  exact h z ξ

theorem theta (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace)
    (hπ : ReferenceCover.CM.CoverProperty B.domainOpen X π)
    (α β : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hα : GeometricSource.CM.RepresentsTheta E L φ X π α) (hβ : GeometricSource.CM.RepresentsTheta E L φ X π β) : α = β := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact raw B.domainOpen X π hπ α.val.val.val β.val.val.val
    (fun z ξ => (hα z ξ).trans (hβ z ξ).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFormUniqueness.CM
