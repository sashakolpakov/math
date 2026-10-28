import OAI.AlgebraicTopology.Kunneth.SimplexFormExtension
import OAI.AlgebraicTopology.Kunneth.SimplexFormMaps
import OAI.AlgebraicTopology.DeRham.Comparison.CubePullbackLocality

/-! # Simplex Form Pullback -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexFormPullback

noncomputable section

/-! Restricting actual manifold differential forms to genuine smooth simplices. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false

open Set Filter _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.Topology Simplicial

namespace Constructions

variable {V W : Type*} {E : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

local instance parameterFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm V n) := inferInstance
local instance parameterFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm V n) := inferInstance

def parameterFormPullback (f : V → M) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm V k :=
  (Analysis.DifferentialForms.Manifold.NormedSpace.smoothFormManifoldEquiv (E := V) (n := k)).symm.toLinearMap.comp
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf)

@[simp] theorem parameterFormPullback_apply (f : V → M)
    (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    parameterFormPullback f hf a = (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf a).toNormedSpace := rfl

theorem parameterFormPullback_d (f : V → M)
    (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    parameterFormPullback f hf (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (parameterFormPullback f hf a) := by
  change (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).toNormedSpace =
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf a).toNormedSpace
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toNormedSpace_d]

theorem parameterFormPullback_congr {S : Set V} (hS : closure (interior S) = S)
    (f g : V → M) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ g) (hfg : EqOn f g S)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    EqOn (parameterFormPullback f hf a) (parameterFormPullback g hg a) S := by
  have hi : EqOn (parameterFormPullback f hf a) (parameterFormPullback g hg a)
      (interior S) := by
    intro x hx
    have he : f =ᶠ[𝓝 x] g := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact hfg (interior_subset hy)
    exact DeRham.Comparison.CubePullbackLocality.normedManifoldPullback_eq_of_eventuallyEq a.val he
  have hc := hi.closure (parameterFormPullback f hf a).smooth.continuous
    (parameterFormPullback g hg a).smooth.continuous
  rwa [hS] at hc

theorem parameterFormPullback_comp (g : W → V) (hg : ContDiff ℝ ∞ g)
    (f : V → M) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    parameterFormPullback (f ∘ g) (hf.comp hg.contMDiff) a =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback g hg (parameterFormPullback f hf a) := by
  ext x v
  change a (f (g x)) (fun i =>
    (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (f ∘ g) x) (v i)) =
    a (f (g x)) (fun i =>
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (g x)) (fderiv ℝ g x (v i)))
  rw [mfderiv_comp x (hf.mdifferentiable (by simp) (g x))
    (hg.contMDiff.mdifferentiable (by simp) x), mfderiv_eq_fderiv]
  rfl

def restrictedManifoldPullback (S : Set V) (f : V → M)
    (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f) (k : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm S k :=
  (RestrictedForms.Constructions.restrictForm S k).comp (parameterFormPullback f hf)

theorem restrictedManifoldPullback_congr {S : Set V} (hS : closure (interior S) = S)
    (f g : V → M) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ g) (hfg : EqOn f g S)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    restrictedManifoldPullback S f hf k a = restrictedManifoldPullback S g hg k a :=
  (RestrictedForms.Constructions.restrictForm_eq_iff S k _ _).mpr (parameterFormPullback_congr hS f g hf hg hfg a)

theorem restrictedManifoldPullback_d {S : Set V} (hS : UniqueDiffOn ℝ S) (f : V → M)
    (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    RestrictedForms.Constructions.restrictedFormD hS k (restrictedManifoldPullback S f hf k a) =
      restrictedManifoldPullback S f hf (k + 1) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) := by
  change RestrictedForms.Constructions.restrictForm S (k + 1) (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (parameterFormPullback f hf a)) =
    RestrictedForms.Constructions.restrictForm S (k + 1) (parameterFormPullback f hf (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a))
  rw [parameterFormPullback_d]

/-- Pull an actual smooth manifold form back to its restriction on a genuine simplex. -/
def simplexManifoldFormRestriction {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) (k : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k →ₗ[ℂ] RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) k :=
  restrictedManifoldPullback (SimplexFormDomain.Constructions.coordinateSimplex n) (SimplexFormExtension.Constructions.globalSimplexParameter sigma)
    (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma) k

theorem simplexManifoldFormRestriction_d {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) k
      (simplexManifoldFormRestriction sigma k a) =
        simplexManifoldFormRestriction sigma (k + 1) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) :=
  restrictedManifoldPullback_d (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) _
    (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma) a

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem globalSimplexParameter_face_eqOn {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    EqOn (SimplexFormExtension.Constructions.globalSimplexParameter
      ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map θ.op sigma))
      (SimplexFormExtension.Constructions.globalSimplexParameter sigma ∘ SimplexFormMaps.Constructions.simplexCoordinateMap θ) (SimplexFormDomain.Constructions.coordinateSimplex m) := by
  intro x hx
  rw [SimplexFormExtension.Constructions.globalSimplexParameter_apply _ x hx]
  change _ = SimplexFormExtension.Constructions.globalSimplexParameter sigma (SimplexFormMaps.Constructions.simplexCoordinateMap θ x)
  rw [SimplexFormExtension.Constructions.globalSimplexParameter_apply sigma _ (SimplexFormMaps.Constructions.simplexCoordinateMap_mapsTo θ hx)]
  change (TopCat.of M).toSSetObjEquiv _ sigma.val
      (Convexity.StdSimplex.map θ (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx)) =
    (TopCat.of M).toSSetObjEquiv _ sigma.val
      (SimplexFormDomain.Constructions.simplexBarycentricPoint (SimplexFormMaps.Constructions.simplexCoordinateMap θ x) (SimplexFormMaps.Constructions.simplexCoordinateMap_mapsTo θ hx))
  apply congrArg ((TopCat.of M).toSSetObjEquiv _ sigma.val)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).injective
  change (Convexity.StdSimplex.map θ (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx) : Fin (n + 1) → ℝ) =
    ((SimplexFormDomain.Constructions.simplexBarycentricPoint (SimplexFormMaps.Constructions.simplexCoordinateMap θ x)
      (SimplexFormMaps.Constructions.simplexCoordinateMap_mapsTo θ hx)).weights : Fin (n + 1) → ℝ)
  rw [← Cohomology.Singular.Smooth.simplexLinearMap_weights, SimplexFormDomain.Constructions.simplexBarycentricPoint_weights,
    SimplexFormDomain.Constructions.simplexBarycentricPoint_weights]
  exact (SimplexFormMaps.Constructions.simplexCoordinateMap_barycentric θ x).symm

/-- Restriction to a face is literally the affine pullback of the restricted form. -/
theorem simplexManifoldFormRestriction_face {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    simplexManifoldFormRestriction
      ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map θ.op sigma) k a =
        SimplexFormMaps.Constructions.simplexFormPullback θ k (simplexManifoldFormRestriction sigma k a) := by
  calc
    _ = restrictedManifoldPullback (SimplexFormDomain.Constructions.coordinateSimplex m)
        (SimplexFormExtension.Constructions.globalSimplexParameter sigma ∘ SimplexFormMaps.Constructions.simplexCoordinateMap θ)
        ((SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma).comp
          (SimplexFormMaps.Constructions.simplexCoordinateMap_contDiff θ).contMDiff) k a :=
      restrictedManifoldPullback_congr (SimplexFormExtension.Constructions.coordinateSimplex_closure_interior m) _ _
        (SimplexFormExtension.Constructions.globalSimplexParameter_smooth _) _ (globalSimplexParameter_face_eqOn θ sigma) a
    _ = _ := by
      change RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex m) k
          (parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma ∘ SimplexFormMaps.Constructions.simplexCoordinateMap θ) _ a) =
        RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex m) k
          (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback (SimplexFormMaps.Constructions.simplexCoordinateMap θ) (SimplexFormMaps.Constructions.simplexCoordinateMap_contDiff θ)
            (parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) (SimplexFormExtension.Constructions.globalSimplexParameter_smooth sigma) a))
      rw [parameterFormPullback_comp]

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexFormPullback
