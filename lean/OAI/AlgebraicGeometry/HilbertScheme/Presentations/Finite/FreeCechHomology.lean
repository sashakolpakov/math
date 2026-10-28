import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FreeCechResidues
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ModuleCechCriterion

/-! # Free Cech Homology -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FreeCechHomology.ProjectiveCech

noncomputable section

/-! In every internal degree, the positive augmented Čech cohomology modules of a finite weighted free polynomial module are finite. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R] [IsNoetherianRing R] (ι : Type w) [Fintype ι]

theorem freeModuleCech_homology_finite (w : ι → ℤ) (d : ℤ) (q : ℕ) :
    Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R (ι →₀ MvPolynomial σ R)
      (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d).homology (q + 1)) :=
  ModuleCechCriterion.ProjectiveCech.moduleCech_homology_finite_of_representatives R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w)
    d q (FreeCechResidues.ProjectiveCech.freeCechResidueAssembly R ι w d).range (FreeCechResidues.ProjectiveCech.freeModuleCech_cycle_mod_finite_range R ι w d q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FreeCechHomology.ProjectiveCech
