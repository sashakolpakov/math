import OAI.AlgebraicTopology.DeRham.Comparison.StarConvexPoincare
import OAI.Analysis.DifferentialForms.Manifold.OpenDeRhamX

/-! # Star Convex -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.StarConvex

noncomputable section

/-!
# Positive-degree de Rham vanishing on open star-convex domains

These are the actual cohomology objects of the smooth exterior-derivative
complex. Exactness follows from the global radial primitive on the domain.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Opens E}

/-- Categorical exactness in a positive degree is precisely existence of
smooth primitives for closed forms in that degree. -/
theorem openDeRhamComplex_exactAt_succ_iff (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).ExactAt (n + 1) ↔
      ∀ form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1), Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d form = 0 →
        ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d primitive = form := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change
    (∀ form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1),
      (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).d (n + 1) (n + 2) form = 0 →
        ∃ primitive : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n,
          (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).d n (n + 1) primitive = form) ↔ _
  simp only [Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex_d]
  rfl

variable [FiniteDimensional ℝ E]

/-- The actual de Rham complex is exact in positive degrees on any open
star-convex domain, about any center. -/
theorem openDeRhamComplex_exactAt_starConvex {c : E}
    (hstar : StarConvex ℝ c (U : Set E)) (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).ExactAt (n + 1) :=
  (openDeRhamComplex_exactAt_succ_iff n).mpr
    (fun form hclosed => Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_starConvex hstar form hclosed)

/-- The actual positive-degree de Rham cohomology object is zero on an open
star-convex domain. -/
theorem openDeRhamCohomology_isZero_starConvex {c : E}
    (hstar : StarConvex ℝ c (U : Set E)) (n : ℕ) :
    Limits.IsZero (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamCohomology U (n + 1)) :=
  (openDeRhamComplex_exactAt_starConvex hstar n).isZero_homology

/-- In particular, the actual de Rham complex is exact in positive degrees
on any open convex domain, including the empty domain. -/
theorem openDeRhamComplex_exactAt_convex (hconvex : Convex ℝ (U : Set E)) (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).ExactAt (n + 1) :=
  (openDeRhamComplex_exactAt_succ_iff n).mpr
    (fun form hclosed => Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.exists_primitive_convex hconvex form hclosed)

/-- Every actual positive-degree de Rham cohomology class vanishes on an
open convex domain. -/
theorem openDeRhamCohomology_isZero_convex (hconvex : Convex ℝ (U : Set E)) (n : ℕ) :
    Limits.IsZero (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamCohomology U (n + 1)) :=
  (openDeRhamComplex_exactAt_convex hconvex n).isZero_homology

end

end OAI.AlgebraicTopology.DeRham.Comparison.StarConvex
