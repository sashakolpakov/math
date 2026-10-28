import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FractionDegrees
import Mathlib.RingTheory.Localization.Module

/-! # Free Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeCoordinates.ProjectiveCech

noncomputable section

/-! Coordinates on the actual localization of a free polynomial module. -/

open _root_.MvPolynomial _root_.Module

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction.GradedModules

universe u v w

variable {σ : Type u}
variable (R : Type v) [CommRing R] (ι : Type w)

def localizedFreeBasis (s : Finset σ) :
    Basis ι (LaurentMonomials.ProjectiveCech.ChartLocalization R s) (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (ι →₀ MvPolynomial σ R) s) :=
  (Finsupp.basisSingleOne (ι := ι) (R := MvPolynomial σ R)).ofIsLocalizedModule (LaurentMonomials.ProjectiveCech.ChartLocalization R s)
    (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s))
    (LocalizedModule.mkLinearMap (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) (ι →₀ MvPolynomial σ R))

def freeLocalizedEquiv (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (ι →₀ MvPolynomial σ R) s ≃ₗ[R] (ι →₀ LaurentMonomials.ProjectiveCech.ChartLocalization R s) :=
  (localizedFreeBasis R ι s).repr.restrictScalars R

theorem freeLocalizedEquiv_mk_one (s : Finset σ) (p : ι →₀ MvPolynomial σ R) (i : ι) :
    freeLocalizedEquiv R ι s (LocalizedModule.mk p 1) i =
      algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R s) (p i) := by
  exact (Finsupp.basisSingleOne (ι := ι) (R := MvPolynomial σ R)).ofIsLocalizedModule_repr_apply
    (LaurentMonomials.ProjectiveCech.ChartLocalization R s) (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s))
    (LocalizedModule.mkLinearMap (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) (ι →₀ MvPolynomial σ R)) p i

theorem freeLocalizedEquiv_fraction (s : Finset σ) (k : ℕ) (p : ι →₀ MvPolynomial σ R) (i : ι) :
    freeLocalizedEquiv R ι s (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k p) i =
      LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k (p i) := by
  let g := LaurentMonomials.ProjectiveCech.inversionMonomial R s
  let L := LaurentMonomials.ProjectiveCech.ChartLocalization R s
  let φ := algebraMap (MvPolynomial σ R) L
  have hu : IsUnit (φ (g ^ k)) := IsLocalization.map_units L (LaurentMonomials.ProjectiveCech.chartDenominator R s k)
  apply hu.mul_right_inj.mp
  rw [LaurentBasis.ProjectiveCech.chartFractionLinearMap_apply]
  have hright : φ (g ^ k) * IsLocalization.mk' L (p i) (LaurentMonomials.ProjectiveCech.chartDenominator R s k) = φ (p i) :=
    IsLocalization.mk'_spec' L (p i) (LaurentMonomials.ProjectiveCech.chartDenominator R s k)
  rw [hright]
  have hclear : g ^ k • Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) g k p =
      LocalizedModule.mk p (1 : Submonoid.powers g) := by
    rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel (Presentations.Module.Fractions.GradedModules.moduleDenominator g k) p
  have he := congrArg (fun x => (localizedFreeBasis R ι s).repr x i) hclear
  rw [← algebraMap_smul L, map_smul, Finsupp.smul_apply, smul_eq_mul] at he
  exact he.trans (freeLocalizedEquiv_mk_one R ι s p i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeCoordinates.ProjectiveCech
