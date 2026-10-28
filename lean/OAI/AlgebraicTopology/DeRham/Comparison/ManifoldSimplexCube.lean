import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension
import OAI.AlgebraicTopology.DeRham.Comparison.DuffyCoordinates

/-! # Manifold Simplex Cube -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSimplexCube

noncomputable section

/-!
# Genuine smooth cubes representing smoothly parametrized simplices

A smooth singular simplex need only have a smooth extension on a neighborhood
of the closed standard simplex. After pulling back that neighborhood by a
smooth cube parametrization, a genuine smooth parameter compression gives a
global smooth cube with the prescribed values on the unit cube. No globally
smooth manifold-valued extension of the simplex is assumed.
-/

open _root_.CategoryTheory Opposite Filter Set OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- Smooth parametrizations into a neighborhood-smooth simplex have global
smooth cube representatives with exactly the prescribed closed-cube values. -/
theorem exists_manifoldCube_of_smoothSimplex_parameter {n k : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (k + 1)), M))
    (hσ : Cohomology.Singular.ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    (parameter : (Fin n → ℝ) → (Fin (k + 1) → ℝ))
    (hparameter : ContDiff ℝ ∞ parameter)
    (himage : MapsTo parameter (StokesF.SingularCubeStokes.unitCube n)
      (Set.range (fun x : Convexity.StdSimplex ℝ (Fin (k + 1)) => (x.weights : Fin (k + 1) → ℝ)))) :
    ∃ cube : ManifoldCubeIntegration.SmoothManifoldCube E M n,
      ∀ (t : Fin n → ℝ) (ht : t ∈ StokesF.SingularCubeStokes.unitCube n),
        cube t = σ (Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofMemRange (parameter t) (himage ht)) := by
  obtain ⟨F, U, hU, hsimplex, hF, hvalues⟩ := hσ
  have hopen : IsOpen (parameter ⁻¹' U) := hU.preimage hparameter.continuous
  have hcube : StokesF.SingularCubeStokes.unitCube n ⊆ parameter ⁻¹' U := fun _ ht => hsimplex (himage ht)
  obtain ⟨compression, hcompression, hrange, hagree⟩ :=
    CubeNeighborhoodExtension.exists_contDiff_cube_compression hopen hcube
  let cube : ManifoldCubeIntegration.SmoothManifoldCube E M n :=
    ⟨F ∘ (parameter ∘ compression),
      hF.comp_contMDiff (hparameter.comp hcompression).contMDiff
        (fun t => hrange (mem_range_self t))⟩
  refine ⟨cube, ?_⟩
  intro t ht
  change F (parameter (compression t)) = _
  have hpoint : compression t = t := hagree.self_of_nhdsSet ht
  rw [hpoint]
  simpa only [Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofMemRange_weights] using
    hvalues (Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofMemRange (parameter t) (himage ht))

/-- The actual Duffy parametrization of a smooth singular simplex admits a
global smooth cube representative, without a global simplex extension. -/
theorem exists_manifoldSimplexCube {n : ℕ}
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    ∃ cube : ManifoldCubeIntegration.SmoothManifoldCube E M n,
      ∀ t : StokesF.SingularCubeStokes.unitCube n,
        cube (t : Fin n → ℝ) =
          (TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val (DuffyCoordinates.Duffy.toSimplex n t) := by
  obtain ⟨cube, hcube⟩ := exists_manifoldCube_of_smoothSimplex_parameter
    ((TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val) σ.property
    (DuffyCoordinates.Duffy.coordinates n) (DuffyCoordinates.Duffy.contDiff_coordinates n ∞)
    (fun _ ht => DuffyCoordinates.Duffy.coordinates_mem_stdSimplex ht)
  refine ⟨cube, ?_⟩
  intro t
  refine (hcube t t.property).trans ?_
  apply congrArg ((TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).injective
  change ((Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofMemRange _ _).weights : Fin (n + 1) → ℝ) =
    (DuffyCoordinates.Duffy.toSimplex n t : Fin (n + 1) → ℝ)
  rw [Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofMemRange_weights, DuffyCoordinates.Duffy.toSimplex_val]

/-- A fixed representative for integrating the actual smooth singular
simplex via the Duffy parametrization. Independence of representatives is
proved using their exact agreement on the closed parameter cube. -/
def manifoldSimplexCube {n : ℕ}
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    ManifoldCubeIntegration.SmoothManifoldCube E M n :=
  Classical.choose (exists_manifoldSimplexCube σ)

theorem manifoldSimplexCube_apply {n : ℕ}
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (t : StokesF.SingularCubeStokes.unitCube n) :
    manifoldSimplexCube σ (t : Fin n → ℝ) =
      (TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val (DuffyCoordinates.Duffy.toSimplex n t) :=
  Classical.choose_spec (exists_manifoldSimplexCube σ) t

/-- The fixed cube agrees on the closed cube with every actual simplex
extension composed with the polynomial Duffy map. The extension itself
need not be globally smooth. -/
theorem manifoldSimplexCube_eqOn_extension {n : ℕ}
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (F : (Fin (n + 1) → ℝ) → M)
    (hvalues : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      F x = (TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val x) :
    EqOn (manifoldSimplexCube σ) (F ∘ DuffyCoordinates.Duffy.coordinates n) (StokesF.SingularCubeStokes.unitCube n) := by
  intro t ht
  simpa only [DuffyCoordinates.Duffy.toSimplex_val, Function.comp_apply] using
    (manifoldSimplexCube_apply σ ⟨t, ht⟩).trans (hvalues (DuffyCoordinates.Duffy.toSimplex n ⟨t, ht⟩)).symm

/-- Every other smooth cube with the same prescribed Duffy values agrees
with the fixed representative on the entire closed unit cube. -/
theorem manifoldSimplexCube_eqOn {n : ℕ}
    (σ : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (cube : ManifoldCubeIntegration.SmoothManifoldCube E M n)
    (hcube : ∀ t : StokesF.SingularCubeStokes.unitCube n, cube (t : Fin n → ℝ) =
      (TopCat.of M).toSSetObjEquiv (op ⦋n⦌) σ.val (DuffyCoordinates.Duffy.toSimplex n t)) :
    EqOn (manifoldSimplexCube σ) cube (StokesF.SingularCubeStokes.unitCube n) := by
  intro t ht
  exact (manifoldSimplexCube_apply σ ⟨t, ht⟩).trans (hcube ⟨t, ht⟩).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSimplexCube
