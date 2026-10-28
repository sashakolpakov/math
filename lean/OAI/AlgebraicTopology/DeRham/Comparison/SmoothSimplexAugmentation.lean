import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldZeroIntegration
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution

/-! # Smooth Simplex Augmentation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation

noncomputable section

/-!
# Degree-zero normalization and augmentation of actual simplex integration

The Duffy integral at degree zero is evaluation at the actual point of the
singular simplex. On every open manifold domain, the genuine locally constant
zero-form inclusion therefore maps to the established point-evaluation
augmentation of smooth singular cochains.
-/

open _root_.CategoryTheory Opposite Set _root_.TopologicalSpace OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open OAI.AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution
open scoped Simplicial _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- The cube chosen for a zero-simplex has exactly its actual point as value. -/
theorem manifoldSimplexCube_zero_point
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋0⦌) :
    (ManifoldSimplexCube.manifoldSimplexCube sigma).toFun 0 = TopCat.toSSetObj₀Equiv sigma.val := by
  have hzero : (0 : Fin 0 → ℝ) ∈ StokesF.SingularCubeStokes.unitCube 0 := by
    constructor <;> intro i <;> exact Fin.elim0 i
  let t : StokesF.SingularCubeStokes.unitCube 0 := ⟨0, hzero⟩
  calc
    (ManifoldSimplexCube.manifoldSimplexCube sigma).toFun 0 =
        (TopCat.of M).toSSetObjEquiv (op ⦋0⦌) sigma.val (DuffyCoordinates.Duffy.toSimplex 0 t) :=
      ManifoldSimplexCube.manifoldSimplexCube_apply sigma t
    _ = (TopCat.of M).toSSetObjEquiv (op ⦋0⦌) sigma.val default :=
      congrArg ((TopCat.of M).toSSetObjEquiv (op ⦋0⦌) sigma.val)
        (Subsingleton.elim _ _)
    _ = TopCat.toSSetObj₀Equiv sigma.val := rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual signed Duffy integral has the required degree-zero normalization. -/
@[simp]
theorem smoothSimplexIntegration_zero
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋0⦌)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    SmoothSimplexIntegration.smoothSimplexIntegration sigma form = form (TopCat.toSSetObj₀Equiv sigma.val) 0 := by
  rw [SmoothSimplexIntegration.smoothSimplexIntegration_apply, pow_zero, one_smul, ManifoldZeroIntegration.manifoldCubeIntegration_zero,
    manifoldSimplexCube_zero_point]

/-- A global locally constant zero-form is sent to its value at the simplex point. -/
theorem smoothSimplexIntegration_locallyConstant
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋0⦌)
    (f : LocallyConstant (⊤ : Opens M) ℂ) :
    SmoothSimplexIntegration.smoothSimplexIntegration sigma
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E ⊤ f)) =
      f ⟨TopCat.toSSetObj₀Equiv sigma.val, by trivial⟩ := by
  rw [smoothSimplexIntegration_zero, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply,
    Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]

/-- On any open set, the intrinsic form of a locally constant section integrates
to exactly the established smooth singular augmentation value. -/
theorem smoothSimplexIntegration_locallyConstant_open (U : Opens M)
    (f : LocallyConstant U ℂ)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet _⦋0⦌) :
    SmoothSimplexIntegration.smoothSimplexIntegration sigma
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f)) =
      f (TopCat.toSSetObj₀Equiv sigma.val) := by
  rw [smoothSimplexIntegration_zero]
  change Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f
    (TopCat.toSSetObj₀Equiv sigma.val) _ = f (TopCat.toSSetObj₀Equiv sigma.val)
  exact Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply U f _ _

variable (E) in
/-- Degree-zero integration of an actual ambient local form into actual smooth
singular cochains of the intrinsic open manifold. -/
def smoothSimplexOpenZeroIntegration (U : Opens M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 →ₗ[ℂ]
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U).X 0 :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).inv.hom.comp
    ((SmoothSimplexIntegration.smoothSimplexIntegrationMap E U 0).comp (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0).toLinearMap)

@[simp]
theorem smoothSimplexOpenZeroIntegration_evaluation (U : Opens M)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet _⦋0⦌) :
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom (smoothSimplexOpenZeroIntegration E U form) sigma =
      SmoothSimplexIntegration.smoothSimplexIntegration sigma (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 form) := by
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).inv
        (SmoothSimplexIntegration.smoothSimplexIntegrationMap E U 0 (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 form))) sigma = _
  rw [Iso.inv_hom_id_apply]
  rfl

/-- Exact augmentation compatibility in each open set, using the actual
integration map and the already constructed locally constant augmentation. -/
theorem smoothSimplexOpenZeroIntegration_augmentation (U : Opens M) :
    (smoothSimplexOpenZeroIntegration E U).comp (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U) =
      ((Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation E M).app (op U)).hom := by
  apply LinearMap.ext
  intro f
  apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
    (ModuleCat.of ℂ ℂ) 0).toLinearEquiv.injective
  funext sigma
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
        (smoothSimplexOpenZeroIntegration E U (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f))
        sigma =
      (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
        (ModuleCat.of ℂ ℂ) 0).hom
          (((Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation E M).app (op U)) f) sigma
  rw [smoothSimplexOpenZeroIntegration_evaluation]
  exact (smoothSimplexIntegration_locallyConstant_open U f sigma).trans
    (Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation_apply E M U f sigma).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation
