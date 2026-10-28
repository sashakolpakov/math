import OAI.AlgebraicTopology.Kunneth.SimplexFormPullback
import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain

/-! # Restricted Simplex Integration -/

namespace OAI.AlgebraicTopology.Kunneth.RestrictedSimplexIntegration

noncomputable section

/-! Actual simplex integration descends to restricted differential forms. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite Set _root_.MeasureTheory
open scoped Simplicial _root_.Manifold ContDiff

namespace Constructions

local instance simplexIntegralFormsAddGroup (m k : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin m → ℝ) k) := inferInstance
local instance simplexIntegralFormsModule (m k : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin m → ℝ) k) := inferInstance

def coordinateIdentitySimplex (n : ℕ) :
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (Fin n → ℝ) (Fin n → ℝ)).toSSet _⦋n⦌ := by
  let f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Fin n → ℝ) :=
    ⟨fun x i => x.weights i.castSucc, continuous_pi fun (i : Fin n) =>
      Convexity.StdSimplex.continuous_weights_apply ℝ i.castSucc⟩
  refine ⟨(TopCat.of (Fin n → ℝ)).toSSetObjEquiv _ |>.symm f, ?_⟩
  change Cohomology.Singular.ManifoldSmooth.IsManifoldSmoothSimplex (Fin n → ℝ) _
  refine ⟨(fun x : Fin (n + 1) → ℝ => fun i : Fin n => x i.castSucc), univ,
    isOpen_univ, subset_univ _, ?_, ?_⟩
  · exact (contDiff_pi.mpr fun (i : Fin n) => contDiff_apply ℝ ℝ i.castSucc).contMDiff.contMDiffOn
  · intro x
    rfl

@[simp] theorem coordinateIdentitySimplex_apply (n : ℕ)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin n) :
    (TopCat.of (Fin n → ℝ)).toSSetObjEquiv _ (coordinateIdentitySimplex n).val x i =
      x.weights i.castSucc := rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem smoothSimplexIntegration_eq_zero_of_image {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      a ((TopCat.of M).toSSetObjEquiv _ sigma.val x) = 0) :
    DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration sigma a = 0 := by
  rw [DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_eq_integral]
  have hzero : (∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
      DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback (DeRham.Comparison.ManifoldSimplexCube.manifoldSimplexCube sigma) a x
        (fun j => Pi.single j 1)) = 0 := by
    have he : (∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
        DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback (DeRham.Comparison.ManifoldSimplexCube.manifoldSimplexCube sigma) a x
          (fun j => Pi.single j 1)) =
        ∫ _x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1), (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change a (DeRham.Comparison.ManifoldSimplexCube.manifoldSimplexCube sigma x) _ = 0
      rw [DeRham.Comparison.ManifoldSimplexCube.manifoldSimplexCube_apply sigma ⟨x, hx⟩, ha]
      rfl
    rw [he, integral_zero]
  rw [hzero, smul_zero]

def rawSimplexIntegral (n : ℕ) : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin n → ℝ) n →ₗ[ℂ] ℂ :=
  (DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (coordinateIdentitySimplex n)).comp
    (Analysis.DifferentialForms.Manifold.NormedSpace.smoothFormManifoldEquiv (E := Fin n → ℝ) (n := n)).toLinearMap

theorem rawSimplexIntegral_vanishing (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin n → ℝ) n)
    (ha : a ∈ RestrictedForms.Constructions.formsVanishingOn (SimplexFormDomain.Constructions.coordinateSimplex n) n) :
    rawSimplexIntegral n a = 0 := by
  apply smoothSimplexIntegration_eq_zero_of_image
  intro x
  have hz := ha (fun i => x.weights i.castSucc) (SimplexFormMaps.Constructions.coordinateSimplex_of_barycentric ⟨x, rfl⟩)
  ext v
  change a (fun i => x.weights i.castSucc) _ = 0
  rw [hz]
  rfl

def simplexIntegral (n : ℕ) : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) n →ₗ[ℂ] ℂ :=
  (RestrictedForms.Constructions.formsVanishingOn (SimplexFormDomain.Constructions.coordinateSimplex n) n).liftQ (rawSimplexIntegral n)
    (fun a ha => rawSimplexIntegral_vanishing n a ha)

@[simp] theorem simplexIntegral_restrict (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin n → ℝ) n) :
    simplexIntegral n (RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) n a) = rawSimplexIntegral n a := rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem globalSimplexParameter_identity_postcompose {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap (Fin n → ℝ) E
      (SimplexFormExtension.Constructions.globalSimplexParameter sigma) (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma)).app _
        (coordinateIdentitySimplex n) = sigma := by
  apply Subtype.ext
  apply ((TopCat.of M).toSSetObjEquiv _).injective
  ext x
  change SimplexFormExtension.Constructions.globalSimplexParameter sigma (fun i => x.weights i.castSucc) =
    (TopCat.of M).toSSetObjEquiv _ sigma.val x
  rw [SimplexFormExtension.Constructions.globalSimplexParameter_apply sigma _ (SimplexFormMaps.Constructions.coordinateSimplex_of_barycentric ⟨x, rfl⟩)]
  apply congrArg ((TopCat.of M).toSSetObjEquiv _ sigma.val)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).injective
  change ((SimplexFormDomain.Constructions.simplexBarycentricPoint _ _).weights : Fin (n + 1) → ℝ) = x.weights
  rw [SimplexFormDomain.Constructions.simplexBarycentricPoint_weights]
  exact SimplexFormMaps.Constructions.simplexBarycentric_recover n x.weights x.total_of_fintype

/-- Restricting a manifold form to its simplex and integrating gives exactly
the repository's original, integration-normalized simplex value. -/
theorem simplexIntegral_manifoldRestriction {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    simplexIntegral n (SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma n a) =
      DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration sigma a := by
  change rawSimplexIntegral n
    (SimplexFormPullback.Constructions.parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma) a) = _
  have he :
      (Analysis.DifferentialForms.Manifold.NormedSpace.smoothFormManifoldEquiv (E := Fin n → ℝ) (n := n))
        (SimplexFormPullback.Constructions.parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma) a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma) a :=
    (Analysis.DifferentialForms.Manifold.NormedSpace.smoothFormManifoldEquiv (E := Fin n → ℝ) (n := n)).apply_symm_apply _
  change DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (coordinateIdentitySimplex n)
    ((Analysis.DifferentialForms.Manifold.NormedSpace.smoothFormManifoldEquiv (E := Fin n → ℝ) (n := n)) _) = _
  rw [he, ← DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_postcompose,
    globalSimplexParameter_identity_postcompose]

theorem simplexManifoldFormRestriction_identity (n k : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin n → ℝ) k) :
    SimplexFormPullback.Constructions.simplexManifoldFormRestriction (coordinateIdentitySimplex n) k a.toManifold =
      RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) k a := by
  have hparam : EqOn (SimplexFormExtension.Constructions.globalSimplexParameter (coordinateIdentitySimplex n)) id (SimplexFormDomain.Constructions.coordinateSimplex n) := by
    intro x hx
    rw [SimplexFormExtension.Constructions.globalSimplexParameter_apply _ x hx]
    funext i
    rw [coordinateIdentitySimplex_apply, SimplexFormDomain.Constructions.simplexBarycentricPoint_weights]
    exact SimplexFormDomain.Constructions.simplexBarycentric_castSucc n x i
  change SimplexFormPullback.Constructions.restrictedManifoldPullback (SimplexFormDomain.Constructions.coordinateSimplex n)
    (SimplexFormExtension.Constructions.globalSimplexParameter (coordinateIdentitySimplex n)) _ k a.toManifold = _
  rw [SimplexFormPullback.Constructions.restrictedManifoldPullback_congr (SimplexFormExtension.Constructions.coordinateSimplex_closure_interior n) _ id
    (SimplexFormExtension.Constructions.globalSimplexParameter_smooth _) contMDiff_id hparam]
  change RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) k
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback id contMDiff_id a.toManifold).toNormedSpace = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_id]
  congr 1

/-- Stokes on the restricted complex is the original smooth-simplex Stokes theorem. -/
theorem simplexIntegral_stokes (n : ℕ) (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex (n + 1)) n) :
    simplexIntegral (n + 1) (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn (n + 1)) n a) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        simplexIntegral n (SimplexFormMaps.Constructions.simplexFormPullback (SimplexCategory.δ j) n a) := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn (SimplexFormDomain.Constructions.coordinateSimplex (n + 1)) n).mkQ_surjective a
  have ha := simplexManifoldFormRestriction_identity (n + 1) n a
  change simplexIntegral (n + 1)
      (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn (n + 1)) n
        (RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex (n + 1)) n a)) = _
  rw [← ha, SimplexFormPullback.Constructions.simplexManifoldFormRestriction_d, simplexIntegral_manifoldRestriction,
    DeRham.Comparison.SmoothSimplexStokes.smoothSimplexStokes]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← simplexIntegral_manifoldRestriction]
  exact congrArg (simplexIntegral n)
    ((SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face (SimplexCategory.δ j)
      (coordinateIdentitySimplex (n + 1)) a.toManifold).trans
        (congrArg (SimplexFormMaps.Constructions.simplexFormPullback (SimplexCategory.δ j) n) ha))

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.RestrictedSimplexIntegration
