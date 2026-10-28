import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ChartCompatibility
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Cech

/-! # Card -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech

noncomputable section

/-! The finite projective Čech differential for actual localized modules. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

abbrev ModuleCechFamily := (s : Finset σ) → Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s

def moduleCechDifferential : ModuleCechFamily (σ := σ) R M →ₗ[R] ModuleCechFamily (σ := σ) R M where
  toFun f s := ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i •
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s) (f (s.erase i))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm r]

def ModuleCechCardSupported (q : ℕ) (f : ModuleCechFamily (σ := σ) R M) : Prop :=
  ∀ s, s.card ≠ q → f s = 0

variable (ℳ : ℤ → Submodule R M)

def ModuleCechHomogeneous (d : ℤ) (f : ModuleCechFamily (σ := σ) R M) : Prop :=
  ∀ s, f s ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d

omit [Fintype σ] in
theorem moduleCechDifferential_card (q : ℕ) (f : ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCechCardSupported R M q f) :
    ModuleCechCardSupported R M (q + 1) (moduleCechDifferential R M f) := by
  intro s hs
  apply Finset.sum_eq_zero
  intro i hi
  have hcard : (s.erase i).card ≠ q := by
    intro h
    exact hs ((Finset.card_erase_add_one hi).symm.trans (congrArg (· + 1) h))
  rw [hf _ hcard, map_zero, smul_zero]

omit [Fintype σ] in
theorem moduleCechDifferential_homogeneous
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    (d : ℤ) (f : ModuleCechFamily (σ := σ) R M) (hf : ModuleCechHomogeneous R M ℳ d f) :
    ModuleCechHomogeneous R M ℳ d (moduleCechDifferential R M f) := by
  intro s
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction_degree R M ℳ (Finset.erase_subset i s) d _ (hf _))

omit [LinearOrder σ] [Module R M] [IsScalarTower R (MvPolynomial σ R) M] in
theorem moduleCech_bounded (q : ℕ) (hq : Fintype.card σ < q)
    (f : ModuleCechFamily (σ := σ) R M) (hf : ModuleCechCardSupported R M q f) : f = 0 := by
  funext s
  apply hf s
  exact ne_of_lt ((Finset.card_le_univ s).trans_lt hq)

variable (ι : Type t)

def freeCechCoordinate (i : ι) (f : ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R)) :
    Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R :=
  fun s => Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (f s) i

theorem freeCechCoordinate_differential (i : ι)
    (f : ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R)) :
    freeCechCoordinate R ι i (moduleCechDifferential R (ι →₀ MvPolynomial σ R) f) =
      Polynomial.Cech.ProjectiveCech.polynomialCechDifferential R (freeCechCoordinate R ι i f) := by
  funext s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (∑ j ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s j •
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (ι →₀ MvPolynomial σ R) (Finset.erase_subset j s) (f (s.erase j))) i = _
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Presentations.Module.ChartCompatibility.ProjectiveCech.freeLocalizedEquiv_restriction]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech
