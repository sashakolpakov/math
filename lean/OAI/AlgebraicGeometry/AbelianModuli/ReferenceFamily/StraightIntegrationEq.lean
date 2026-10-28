import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodEdgesTo
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration

/-! # Straight Integration Eq -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StraightIntegrationEq.StraightIntegration

noncomputable section

/-!
# ReferenceFamily: integration on straight singular edges

The straight edge has a genuine smooth extension. Integration of a constant
one-form on that edge is evaluation on its displacement, with the project's
Duffy orientation convention included.
-/

open _root_.CategoryTheory Opposite Set _root_.MeasureTheory
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial _root_.Manifold ContDiff

open OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodEdgesTo.PeriodEdges

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual straight singular edge is linear in its barycentric coordinate. -/
theorem vectorEdge_simplex (v : V) (x : Convexity.StdSimplex ℝ (Fin 2)) :
    (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := V)).toSSetObjEquiv (op ⦋1⦌) (PeriodEdgesTo.PeriodEdges.vectorEdge v) x = x.weights 1 • v := by
  unfold PeriodEdgesTo.PeriodEdges.vectorEdge TopCat.toSSetObj₁Equiv
  change (Path.segment (0 : V) v) (Convexity.StdSimplex.homeomorphI x) = x.weights 1 • v
  simp [Path.segment_apply, AffineMap.lineMap_apply, Convexity.StdSimplex.homeomorphI_apply_coe]

/-- The straight edge extends smoothly to the whole barycentric vector space. -/
def smoothVectorEdge (v : V) : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex V V).toSSet _⦋1⦌ :=
  ⟨PeriodEdgesTo.PeriodEdges.vectorEdge v, by
    refine ⟨fun x : Fin 2 → ℝ => x 1 • v, univ, isOpen_univ, subset_univ _, ?_, ?_⟩
    · exact ((contDiff_apply (𝕜 := ℝ) (E := ℝ) 1).smul contDiff_const).contMDiff.contMDiffOn
    · intro x
      exact (vectorEdge_simplex v x).symm⟩

/-- Its Duffy cube travels from v to zero, before the orientation correction. -/
def straightDuffyCube (v : V) : AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube V V 1 :=
  ⟨fun t : Fin 1 → ℝ => (1 - t 0) • v,
    ((contDiff_const.sub (contDiff_apply (𝕜 := ℝ) (E := ℝ) 0)).smul
      contDiff_const).contMDiff⟩

theorem straightDuffyCube_eq (v : V) (t : AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes.unitCube 1) :
    straightDuffyCube v t.val =
      (TopCat.of V).toSSetObjEquiv _ (smoothVectorEdge v).val (AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy.toSimplex 1 t) := by
  erw [vectorEdge_simplex]
  change (1 - t.val 0) • v = (AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy.toSimplex 1 t : Fin 2 → ℝ) 1 • v
  rw [AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy.toSimplex_val]
  change (1 - t.val 0) • v = ((1 - t.val 0) * 1) • v
  rw [mul_one]

/-- Integration of a constant actual manifold one-form has the standard sign. -/
theorem smoothVectorEdge_integration
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V V 1) (α : V [⋀^Fin 1]→L[ℝ] ℂ)
    (hform : ∀ x : V, form x = α) (v : V) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (smoothVectorEdge v) form = α (fun _ => v) := by
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_eq_cube _ (straightDuffyCube v)
    (straightDuffyCube_eq v) form, AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral]
  have hder (x : Fin 1 → ℝ) :
      HasFDerivAt (fun t : Fin 1 → ℝ => (1 - t 0) • v)
        ((-(ContinuousLinearMap.proj (R := ℝ) (i := 0))).smulRight v) x := by
    simpa only [zero_sub] using! ((hasFDerivAt_const (1 : ℝ) x).sub
      (ContinuousLinearMap.proj (R := ℝ) (i := 0)).hasFDerivAt).smul_const v
  have hval (x : Fin 1 → ℝ) :
      AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback (straightDuffyCube v) form x (fun j => Pi.single j 1) =
        -α (fun _ => v) := by
    change form ((1 - x 0) • v)
      (fun i => mfderiv (𝓘(ℝ, Fin 1 → ℝ)) (𝓘(ℝ, V))
        (fun t : Fin 1 → ℝ => (1 - t 0) • v) x (Pi.single i 1)) = _
    rw [hform, (hder x).hasMFDerivAt.mfderiv]
    change α (fun i : Fin 1 => (-((Pi.single i (1 : ℝ) : Fin 1 → ℝ) 0)) • v) = _
    have he : (fun i : Fin 1 => (-((Pi.single i (1 : ℝ) : Fin 1 → ℝ) 0)) • v) =
        fun _ : Fin 1 => -v := by
      funext i
      fin_cases i
      simp
    rw [he]
    simpa using α.map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => v)
  simp_rw [hval]
  simp [Measure.real, Real.volume_Icc_pi]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StraightIntegrationEq.StraightIntegration
