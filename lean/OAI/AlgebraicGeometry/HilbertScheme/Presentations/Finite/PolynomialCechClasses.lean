import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechResidueIdentity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialResidues

/-! # Polynomial Cech Classes -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialCechClasses.ProjectiveCech

noncomputable section

/-! Every homogeneous polynomial Čech cocycle is congruent modulo actual boundaries to an element of an explicit finite coefficient module. -/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R]

theorem polynomialCech_cycle_mod_finite_range (d : ℤ) (q : ℕ)
    (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Polynomial.Cech.ProjectiveCech.CechHomogeneous R d f)
    (hcard : Polynomial.Cech.ProjectiveCech.CechCardSupported R (q + 1) f) (hcycle : Polynomial.Cech.ProjectiveCech.polynomialCechDifferential R f = 0) :
    ∃ g : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R,
      Polynomial.Cech.ProjectiveCech.CechHomogeneous R d g ∧ Polynomial.Cech.ProjectiveCech.CechCardSupported R q g ∧
        f - Polynomial.Cech.ProjectiveCech.polynomialCechDifferential R g ∈ (PolynomialResidues.ProjectiveCech.polynomialResidueAssembly (σ := σ) R d).range := by
  obtain ⟨g, hg, hgc, hgd⟩ := Polynomial.CechResidueIdentity.ProjectiveCech.polynomialCech_cycle_mod_top_residue R d q f hf hcard hcycle
  refine ⟨g, hg, hgc, ?_⟩
  have heq : f - Polynomial.Cech.ProjectiveCech.polynomialCechDifferential R g = Polynomial.TopResidue.ProjectiveCech.polynomialTopResidue R f := by
    rw [hgd]
    abel
  rw [heq]
  exact PolynomialResidues.ProjectiveCech.polynomialTopResidue_mem_finite_range R d f hf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialCechClasses.ProjectiveCech
