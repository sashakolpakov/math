import OAI.AlgebraicTopology.Kunneth.SimplexFormDomain
import OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmooth

/-! # Simplex Form Extension -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexFormExtension

noncomputable section

/-! Global smooth parameters for genuine smooth simplices, with agreement on the simplex. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false

open Filter Set _root_.CategoryTheory Opposite
open scoped _root_.Topology ContDiff _root_.Manifold Simplicial

namespace Constructions

theorem coordinateSimplex_closure_interior (n : ℕ) :
    closure (interior (SimplexFormDomain.Constructions.coordinateSimplex n)) = SimplexFormDomain.Constructions.coordinateSimplex n := by
  rw [(SimplexFormDomain.Constructions.coordinateSimplex_convex n).closure_interior_eq_closure_of_nonempty_interior
    (SimplexFormDomain.Constructions.coordinateSimplex_interior_nonempty n), (SimplexFormDomain.Constructions.coordinateSimplex_isClosed n).closure_eq]

/-- Smoothly compress the entire coordinate space into any neighborhood of
the closed coordinate simplex, fixing a neighborhood of the simplex. -/
theorem exists_simplexCompression {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hKU : SimplexFormDomain.Constructions.coordinateSimplex n ⊆ U) :
    ∃ g : (Fin n → ℝ) → (Fin n → ℝ), ContDiff ℝ ∞ g ∧ range g ⊆ U ∧
      g =ᶠ[𝓝ˢ (SimplexFormDomain.Constructions.coordinateSimplex n)] id := by
  obtain ⟨δ, hδ, hδU⟩ := (SimplexFormDomain.Constructions.coordinateSimplex_isCompact n).exists_thickening_subset_open hU hKU
  let V : Set (Fin n → ℝ) := Metric.thickening δ (SimplexFormDomain.Constructions.coordinateSimplex n)
  have hV : IsOpen V := Metric.isOpen_thickening
  have hKV : SimplexFormDomain.Constructions.coordinateSimplex n ⊆ V := Metric.self_subset_thickening hδ _
  have hVconv : Convex ℝ V := (SimplexFormDomain.Constructions.coordinateSimplex_convex n).thickening δ
  have h0V : (0 : Fin n → ℝ) ∈ V := hKV (SimplexFormDomain.Constructions.coordinateSimplex_zero n)
  obtain ⟨rho, hone, hzeroOutside, hrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, Fin n → ℝ))
      (s := SimplexFormDomain.Constructions.coordinateSimplex n) (t := V) (SimplexFormDomain.Constructions.coordinateSimplex_isClosed n)
      (by simpa only [hV.interior_eq] using hKV) (n := ⊤)
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => rho x • x
  refine ⟨g, rho.contMDiff.contDiff.smul contDiff_id, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ V
    · apply hδU
      have hcomb := hVconv hx h0V (hrange x).1
        (sub_nonneg.mpr (hrange x).2) (by ring : rho x + (1 - rho x) = 1)
      simpa only [smul_zero, add_zero] using hcomb
    · have hrho : rho x = 0 := hzeroOutside x hx
      simpa only [g, hrho, zero_smul] using hKU (SimplexFormDomain.Constructions.coordinateSimplex_zero n)
  · filter_upwards [hone] with x hx
    change rho x • x = x
    rw [hx, one_smul]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- A genuine smooth singular simplex has a globally smooth coordinate
parameterization with exactly its original values on the closed simplex. -/
theorem exists_globalSimplexParameter {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    ∃ g : (Fin n → ℝ) → M, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, E) ∞ g ∧
      ∀ (x : Fin n → ℝ) (hx : x ∈ SimplexFormDomain.Constructions.coordinateSimplex n),
        g x = (TopCat.of M).toSSetObjEquiv _ sigma.val
          (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx) := by
  obtain ⟨F, U, hU, hsub, hF, hvalues⟩ := sigma.property
  have hopen : IsOpen (SimplexFormDomain.Constructions.simplexBarycentric n ⁻¹' U) :=
    hU.preimage (SimplexFormDomain.Constructions.simplexBarycentric_contDiff n).continuous
  have hS : SimplexFormDomain.Constructions.coordinateSimplex n ⊆ SimplexFormDomain.Constructions.simplexBarycentric n ⁻¹' U :=
    fun _ hx => hsub (SimplexFormDomain.Constructions.simplexBarycentric_mem hx)
  obtain ⟨r, hr, hrange, hid⟩ := exists_simplexCompression hopen hS
  refine ⟨F ∘ (SimplexFormDomain.Constructions.simplexBarycentric n ∘ r), ?_, ?_⟩
  · exact hF.comp_contMDiff ((SimplexFormDomain.Constructions.simplexBarycentric_contDiff n).comp hr).contMDiff
      (fun x => hrange (mem_range_self x))
  · intro x hx
    change F (SimplexFormDomain.Constructions.simplexBarycentric n (r x)) = _
    rw [hid.self_of_nhdsSet hx]
    simpa only [SimplexFormDomain.Constructions.simplexBarycentricPoint_weights, id_eq] using hvalues (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx)

def globalSimplexParameter {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    (Fin n → ℝ) → M :=
  (exists_globalSimplexParameter sigma).choose

theorem globalSimplexParameter_smooth {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, E) ∞ (globalSimplexParameter sigma) :=
  (exists_globalSimplexParameter sigma).choose_spec.1

theorem globalSimplexParameter_apply {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (x : Fin n → ℝ) (hx : x ∈ SimplexFormDomain.Constructions.coordinateSimplex n) :
    globalSimplexParameter sigma x = (TopCat.of M).toSSetObjEquiv _ sigma.val
      (SimplexFormDomain.Constructions.simplexBarycentricPoint x hx) :=
  (exists_globalSimplexParameter sigma).choose_spec.2 x hx

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexFormExtension
