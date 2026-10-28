import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeCechLinearAssembly
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialCechClasses

/-! # Free Cech Residues -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FreeCechResidues.ProjectiveCech

noncomputable section

/-! Actual homogeneous Čech cycles of a finite weighted free polynomial module have representatives in a finite coefficient module. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R] (ι : Type w) [Fintype ι]

def freeCechResidueAssembly (w : ι → ℤ) (d : ℤ) :
    ((i : ι) → PolynomialResidues.ProjectiveCech.polynomialResidueCoefficientModule (σ := σ) R (d - w i)) →ₗ[R]
      ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R) :=
  (FreeCechLinearAssembly.ProjectiveCech.freeCechAssembleLinear R ι).comp (LinearMap.pi (fun i =>
    (PolynomialResidues.ProjectiveCech.polynomialResidueAssembly (σ := σ) R (d - w i)).comp (LinearMap.proj i)))

omit [Nonempty σ] in
theorem freeCechCoordinate_residueAssembly (w : ι → ℤ) (d : ℤ)
    (c : (i : ι) → PolynomialResidues.ProjectiveCech.polynomialResidueCoefficientModule (σ := σ) R (d - w i)) (i : ι) :
    ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i (freeCechResidueAssembly R ι w d c) =
      PolynomialResidues.ProjectiveCech.polynomialResidueAssembly (σ := σ) R (d - w i) (c i) :=
  FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble R ι (fun j => PolynomialResidues.ProjectiveCech.polynomialResidueAssembly (σ := σ) R (d - w j) (c j)) i

instance freeCechResidueAssembly_finite_range (w : ι → ℤ) (d : ℤ) :
    Module.Finite R (freeCechResidueAssembly (σ := σ) R ι w d).range := by
  infer_instance

theorem freeModuleCech_cycle_mod_finite_range (w : ι → ℤ) (d : ℤ) (q : ℕ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R))
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d f)
    (hcard : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) (q + 1) f)
    (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) f = 0) :
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R),
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d g ∧
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) q g ∧
      f - ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) g ∈ (freeCechResidueAssembly R ι w d).range := by
  have hcoord (i : ι) : Polynomial.Cech.ProjectiveCech.CechHomogeneous R (d - w i) (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) :=
    fun s => Localized.FreeDegrees.ProjectiveCech.freeLocalizedEquiv_degree R w s d (f s) (hf s) i
  have hcoordcard (i : ι) : Polynomial.Cech.ProjectiveCech.CechCardSupported R (q + 1) (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) := by
    intro s hs
    change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (f s) i = 0
    rw [hcard s hs, map_zero, Finsupp.zero_apply]
  have hcoordcycle (i : ι) : Polynomial.Cech.ProjectiveCech.polynomialCechDifferential R (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) = 0 := by
    rw [← ModuleCech.Card.ProjectiveCech.freeCechCoordinate_differential, hcycle, FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_zero]
  choose g hg hgc hres using fun i => PolynomialCechClasses.ProjectiveCech.polynomialCech_cycle_mod_finite_range R (d - w i) q
    (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) (hcoord i) (hcoordcard i) (hcoordcycle i)
  choose c hc using hres
  refine ⟨FreeModuleCechExactness.ProjectiveCech.freeCechAssemble R ι g, FreeModuleCechExactness.ProjectiveCech.freeCechAssemble_homogeneous R ι w d g hg,
    FreeModuleCechExactness.ProjectiveCech.freeCechAssemble_card R ι q g hgc, c, ?_⟩
  apply FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_ext R ι
  intro i
  rw [freeCechCoordinate_residueAssembly, FreeCechLinearAssembly.ProjectiveCech.freeCechCoordinate_sub, ModuleCech.Card.ProjectiveCech.freeCechCoordinate_differential,
    FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble]
  exact hc i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FreeCechResidues.ProjectiveCech
