import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ
import OAI.AlgebraicTopology.DeRham.Comparison.NormalizedMap
import OAI.Analysis.DifferentialForms.Manifold.DeRhamPullback

/-! # Normalized Integration Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.NormalizedIntegrationNaturality

noncomputable section

/-!
# Naturality of the genuine normalized cubical integration map

The chain map is induced by actual postcomposition of smooth cubes. The form
map is the actual derivative pullback. The integral identity follows from
the chain rule, and descends to normalized chains and their cohomology.
-/

open _root_.CategoryTheory Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m l q : ℕ}

/-- The genuine pullback integrand respects composition of the smooth maps. -/
theorem complexCubeIntegrand_postcompose
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f)
    (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin l → ℝ) n)
    (x : Fin n → ℝ) :
    ComplexCubeIntegration.complexCubeIntegrand (CubicalDegenerateQ.cubePostcompose f hf σ) form x =
      ComplexCubeIntegration.complexCubeIntegrand σ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form) x := by
  change form (f (σ.toFun x))
      (fun j => fderiv ℝ (f ∘ σ.toFun) x (Pi.single j 1)) =
    form (f (σ.toFun x))
      (fun j => fderiv ℝ f (σ.toFun x) (fderiv ℝ σ.toFun x (Pi.single j 1)))
  rw [fderiv_comp x ((hf.differentiable (by simp)).differentiableAt)
    ((σ.smooth.differentiable (by simp)).differentiableAt)]
  rfl

/-- Integrating a pulled-back form equals integrating on the postcomposed cube. -/
theorem complexIntegrateForm_postcompose
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f)
    (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin l → ℝ) n) :
    ComplexCubeIntegration.complexIntegrateForm (CubicalDegenerateQ.cubePostcompose f hf σ) form =
      ComplexCubeIntegration.complexIntegrateForm σ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form) := by
  rw [ComplexCubeIntegration.complexIntegrateForm_eq_integral (CubicalDegenerateQ.cubePostcompose f hf σ) form form.smooth,
    ComplexCubeIntegration.complexIntegrateForm_eq_integral σ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form)
      (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form).smooth]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  exact complexCubeIntegrand_postcompose f hf σ form x

/-- Naturality extends to every actual finite integral chain. -/
theorem complexRawCubicalIntegration_postcompose
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f)
    (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin l → ℝ) n) (c : StokesF.SingularCubeStokes.SingularChain n m) :
    ComplexNormalizedIntegration.complexRawCubicalIntegration form (CubicalDegenerateQ.rawCubeMap f hf n c) =
      ComplexNormalizedIntegration.complexRawCubicalIntegration (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form) c := by
  have h : (ComplexNormalizedIntegration.complexRawCubicalIntegration form).comp (CubicalDegenerateQ.rawCubeMap f hf n) =
      ComplexNormalizedIntegration.complexRawCubicalIntegration (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form) := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply, CubicalDegenerateQ.rawCubeMap_single, ComplexNormalizedIntegration.complexRawCubicalIntegration_single,
      complexIntegrateForm_postcompose]
  exact LinearMap.congr_fun h c

/-- The integral identity descends to the actual normalized chain quotient. -/
theorem normalizedComplexIntegration_postcompose
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f)
    (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin l → ℝ) n) (c : CubicalDegenerateQ.NormalizedCubicalChain n m) :
    ComplexNormalizedIntegration.normalizedComplexIntegration form (CubicalDegenerateQ.normalizedCubeMap f hf n c) =
      ComplexNormalizedIntegration.normalizedComplexIntegration (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form) c := by
  obtain ⟨raw, rfl⟩ := (CubicalDegenerateQ.degenerateSubmodule n m).mkQ_surjective c
  change ComplexNormalizedIntegration.complexRawCubicalIntegration form (CubicalDegenerateQ.rawCubeMap f hf n raw) =
    ComplexNormalizedIntegration.complexRawCubicalIntegration (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback f hf form) raw
  exact complexRawCubicalIntegration_postcompose f hf form raw

/-- Pullback of cochains is precomposition by the genuine normalized chain map. -/
def normalizedCubicalCochainPullback
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ComplexNormalizedStokes.NormalizedComplexCubicalCochain n l →ₗ[ℂ] ComplexNormalizedStokes.NormalizedComplexCubicalCochain n m where
  toFun phi := phi.comp (CubicalDegenerateQ.normalizedCubeMap f hf n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual smooth maps induce morphisms of normalized cubical cochain complexes. -/
def normalizedCubicalPullback (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f) :
    NormalizedMap.normalizedComplexCochainComplex l ⟶ NormalizedMap.normalizedComplexCochainComplex m :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (normalizedCubicalCochainPullback f hf n))
    (fun n => by
      rw [NormalizedMap.normalizedComplexCochainComplex_d, NormalizedMap.normalizedComplexCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro phi
      change ComplexNormalizedStokes.NormalizedComplexCubicalCochain n l at phi
      apply LinearMap.ext
      intro c
      change phi (CubicalDegenerateQ.normalizedCubeMap f hf n (CubicalDegenerateQ.normalizedBoundary n m c)) =
        phi (CubicalDegenerateQ.normalizedBoundary n l (CubicalDegenerateQ.normalizedCubeMap f hf (n + 1) c))
      rw [CubicalDegenerateQ.normalizedCubeMap_boundary])

@[simp]
theorem normalizedCubicalPullback_id (m : ℕ) :
    normalizedCubicalPullback (id : (Fin m → ℝ) → _) contDiff_id =
      𝟙 (NormalizedMap.normalizedComplexCochainComplex m) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change ComplexNormalizedStokes.NormalizedComplexCubicalCochain n m at phi
  apply LinearMap.ext
  intro c
  change phi (CubicalDegenerateQ.normalizedCubeMap id contDiff_id n c) = phi c
  rw [CubicalDegenerateQ.normalizedCubeMap_id]
  rfl

theorem normalizedCubicalPullback_comp
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f)
    (g : (Fin l → ℝ) → (Fin q → ℝ)) (hg : ContDiff ℝ ∞ g) :
    normalizedCubicalPullback (g ∘ f) (hg.comp hf) =
      normalizedCubicalPullback g hg ≫ normalizedCubicalPullback f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change ComplexNormalizedStokes.NormalizedComplexCubicalCochain n q at phi
  apply LinearMap.ext
  intro c
  change phi (CubicalDegenerateQ.normalizedCubeMap (g ∘ f) (hg.comp hf) n c) =
    phi (CubicalDegenerateQ.normalizedCubeMap g hg n (CubicalDegenerateQ.normalizedCubeMap f hf n c))
  rw [CubicalDegenerateQ.normalizedCubeMap_comp]
  rfl

/-- Naturality of integration as an equality of actual cochain morphisms. -/
theorem deRhamToNormalizedCubical_naturality
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f) :
    Analysis.DifferentialForms.Manifold.DeRhamPullback.deRhamPullback f hf ≫ NormalizedMap.deRhamToNormalizedCubical m =
      NormalizedMap.deRhamToNormalizedCubical l ≫ normalizedCubicalPullback f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  apply LinearMap.ext
  intro c
  exact (normalizedComplexIntegration_postcompose f hf form c).symm

/-- Pullback on the actual normalized cubical cohomology objects. -/
def normalizedCubicalCohomologyPullback
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    (NormalizedMap.normalizedComplexCochainComplex l).homology n ⟶
      (NormalizedMap.normalizedComplexCochainComplex m).homology n :=
  HomologicalComplex.homologyMap (normalizedCubicalPullback f hf) n

/-- Naturality persists on the genuine induced cohomology maps. -/
theorem deRhamToNormalizedCubicalCohomology_naturality
    (f : (Fin m → ℝ) → (Fin l → ℝ)) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.DeRhamPullback.deRhamCohomologyPullback f hf n ≫
      NormalizedMap.deRhamToNormalizedCubicalCohomology m n =
    NormalizedMap.deRhamToNormalizedCubicalCohomology l n ≫
      normalizedCubicalCohomologyPullback f hf n := by
  change HomologicalComplex.homologyMap (Analysis.DifferentialForms.Manifold.DeRhamPullback.deRhamPullback f hf) n ≫
      HomologicalComplex.homologyMap (NormalizedMap.deRhamToNormalizedCubical m) n =
    HomologicalComplex.homologyMap (NormalizedMap.deRhamToNormalizedCubical l) n ≫
      HomologicalComplex.homologyMap (normalizedCubicalPullback f hf) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun F => HomologicalComplex.homologyMap F n)
    (deRhamToNormalizedCubical_naturality f hf)

end

end OAI.AlgebraicTopology.DeRham.Comparison.NormalizedIntegrationNaturality
