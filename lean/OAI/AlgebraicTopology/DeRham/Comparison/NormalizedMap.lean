import OAI.AlgebraicTopology.DeRham.Comparison.ComplexNormalizedStokes
import OAI.Analysis.DifferentialForms.Manifold.DeRham

/-! # Normalized Map -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.NormalizedMap

noncomputable section

/-!
# The actual de Rham integration morphism into normalized cubical cochains

This packages the already constructed normalized cubical coboundary and
integration functionals in mathlib's category of cochain complexes. It also
constructs the induced cohomology map. No quasi-isomorphism or comparison with
continuous singular cohomology is asserted here.
-/

open _root_.CategoryTheory

/-- The complex-valued dual of the actual normalized smooth cubical chain complex. -/
def normalizedComplexCochainComplex (m : ℕ) : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (ComplexNormalizedStokes.NormalizedComplexCubicalCochain n m))
    (fun n => ModuleCat.ofHom (ComplexNormalizedStokes.normalizedComplexCoboundary n m))
    (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro phi
      exact ComplexNormalizedStokes.normalizedComplexCoboundary_squared phi)

@[simp]
theorem normalizedComplexCochainComplex_d (m n : ℕ) :
    (normalizedComplexCochainComplex m).d n (n + 1) =
      ModuleCat.ofHom (ComplexNormalizedStokes.normalizedComplexCoboundary n m) :=
  CochainComplex.of_d
    (fun j => ModuleCat.of ℂ (ComplexNormalizedStokes.NormalizedComplexCubicalCochain j m))
    (fun j => ModuleCat.ofHom (ComplexNormalizedStokes.normalizedComplexCoboundary j m)) n

/-- The integration cochain morphism, with its differential equation proved by Stokes. -/
def deRhamToNormalizedCubical (m : ℕ) :
    Analysis.DifferentialForms.Manifold.DeRham.deRhamComplex (Fin m → ℝ) ⟶ normalizedComplexCochainComplex m :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (ComplexNormalizedIntegration.normalizedComplexIntegrationLinearMap (n := n) (m := m)))
    (fun _ => by
      rw [Analysis.DifferentialForms.Manifold.DeRham.deRhamComplex_d, normalizedComplexCochainComplex_d]
      apply ModuleCat.hom_ext
      exact ComplexNormalizedStokes.normalizedComplexIntegrationLinearMap_d)

@[simp]
theorem deRhamToNormalizedCubical_f_apply (m n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin m → ℝ) n) :
    (deRhamToNormalizedCubical m).f n form = ComplexNormalizedIntegration.normalizedComplexIntegration form := rfl

/-- The resulting map on the actual kernel/image cohomology objects. -/
def deRhamToNormalizedCubicalCohomology (m n : ℕ) :
    Analysis.DifferentialForms.Manifold.DeRham.deRhamCohomology (Fin m → ℝ) n ⟶
      (normalizedComplexCochainComplex m).homology n :=
  HomologicalComplex.homologyMap (deRhamToNormalizedCubical m) n

/-- Integrating a closed representative and then taking its class agrees with
the induced cohomology map. -/
theorem deRhamToNormalizedCubical_class (m n : ℕ) :
    (Analysis.DifferentialForms.Manifold.DeRham.deRhamComplex (Fin m → ℝ)).homologyπ n ≫
      deRhamToNormalizedCubicalCohomology m n =
    HomologicalComplex.cyclesMap (deRhamToNormalizedCubical m) n ≫
      (normalizedComplexCochainComplex m).homologyπ n :=
  HomologicalComplex.homologyπ_naturality (deRhamToNormalizedCubical m) n

end

end OAI.AlgebraicTopology.DeRham.Comparison.NormalizedMap
