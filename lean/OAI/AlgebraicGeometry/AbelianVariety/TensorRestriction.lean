import OAI.AlgebraicGeometry.AbelianVariety.SimplexWedge
import OAI.AlgebraicTopology.Products.Cup
import OAI.AlgebraicTopology.Kunneth.TensorSimplicialForms

/-! # Tensor Restriction -/

namespace OAI.AlgebraicGeometry.AbelianVariety.TensorRestriction.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial TensorProduct
open OAI.AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions OAI.AlgebraicTopology.Products.Cup

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n p q : ℕ}

def closedSimplexRestriction
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) : AlgebraicTopology.Kunneth.SimplicialForms.Constructions.SimplexClosedForms n q :=
  ⟨AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b.val, by
    rw [LinearMap.mem_ker, AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction_d, b.property, map_zero]⟩

def tensorSimplexRestriction
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p :=
  AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a ⊗ₜ[ℂ] closedSimplexRestriction sigma b

theorem tensorSimplexRestriction_d
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    tensorSimplexRestriction sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) b =
      AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorD q n p (tensorSimplexRestriction sigma a b) := by
  simp only [tensorSimplexRestriction, AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorD_tmul, AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction_d]

theorem closedSimplexRestriction_face {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    closedSimplexRestriction ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map θ.op sigma) b =
      AlgebraicTopology.Kunneth.SimplicialForms.Constructions.simplexClosedFormPullback θ q (closedSimplexRestriction sigma b) := by
  apply Subtype.ext
  exact AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face θ sigma b.val

theorem tensorSimplexRestriction_face {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    tensorSimplexRestriction ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map θ.op sigma) a b =
      AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorPullback θ q p (tensorSimplexRestriction sigma a b) := by
  simp only [tensorSimplexRestriction, AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorPullback, TensorProduct.map_tmul,
    AlgebraicTopology.Kunneth.SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face, closedSimplexRestriction_face]

def modelFunctionalCochain (F : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X n :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) n).inv
    (fun sigma => F (tensorSimplexRestriction sigma a b))

theorem modelFunctionalCochain_evaluation (F : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q)
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ) sigma
      (modelFunctionalCochain F a b) = F (tensorSimplexRestriction sigma a b) := by
  rw [← AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  exact congrFun
    ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) n).toLinearEquiv.apply_symm_apply _) sigma

theorem simplexFormTensorDelta_apply (F : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (x : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q (n + 1) p) :
    AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorDelta q n p F x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        F (AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorPullback (SimplexCategory.δ i) q p x) := by
  change F ((∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    ModuleCat.ofHom (AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorPullback (SimplexCategory.δ i) q p)) x) = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, ModuleCat.hom_ofHom, map_sum, map_zsmul]

theorem modelFunctionalCochain_coboundary (F : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d n (n + 1) (modelFunctionalCochain F a b) =
      modelFunctionalCochain (AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorDelta q n p F) a b := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_coboundary_apply, modelFunctionalCochain_evaluation, simplexFormTensorDelta_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [modelFunctionalCochain_evaluation]
  exact congrArg (fun x => (-1 : ℤ) ^ i.val • F x)
    (tensorSimplexRestriction_face (SimplexCategory.δ i) sigma a b)

theorem tensorSimplexRestriction_closed
    (sigma : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorD q n p (tensorSimplexRestriction sigma a.val b) = 0 := by
  rw [← tensorSimplexRestriction_d, a.property]
  simp only [tensorSimplexRestriction, map_zero, TensorProduct.zero_tmul]

/-- A model functional factoring through the differential vanishes on closed global forms. -/
theorem modelFunctionalCochain_factor_zero
    (F : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (H : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n (p + 1) →ₗ[ℂ] ℂ)
    (hH : H.comp (AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorD q n p) = F)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    modelFunctionalCochain F a.val b = 0 := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [modelFunctionalCochain_evaluation, map_zero]
  rw [← hH, LinearMap.comp_apply, tensorSimplexRestriction_closed, map_zero]

/-- A model homotopy gives a literal coboundary on the actual smooth singular complex. -/
theorem modelFunctionalCochain_homotopy_boundary
    (F : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q (n + 1) p →ₗ[ℂ] ℂ)
    (H : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q (n + 1) (p + 1) →ₗ[ℂ] ℂ)
    (P : AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] ℂ)
    (hH : H.comp (AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorD q (n + 1) p) =
      F - AlgebraicTopology.Kunneth.TensorSimplicialForms.Constructions.simplexFormTensorDelta q n p P)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d n (n + 1)
      (modelFunctionalCochain P a.val b) = modelFunctionalCochain F a.val b := by
  rw [modelFunctionalCochain_coboundary]
  apply AlgebraicTopology.Products.Cup.cochain_ext (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet (ModuleCat.of ℂ ℂ)
  intro sigma
  rw [modelFunctionalCochain_evaluation, modelFunctionalCochain_evaluation]
  have he := LinearMap.congr_fun hH (tensorSimplexRestriction sigma a.val b)
  simp only [LinearMap.comp_apply, tensorSimplexRestriction_closed, map_zero,
    LinearMap.sub_apply] at he
  exact (sub_eq_zero.mp he.symm).symm

end

end OAI.AlgebraicGeometry.AbelianVariety.TensorRestriction.Constructions.ExteriorCohomology
