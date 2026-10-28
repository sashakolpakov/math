import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Differential

/-! # Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Cech.ProjectiveCech

noncomputable section

/-!
The augmented finite Čech differential on actual polynomial localizations.
The empty subset is the augmentation term; subsets of cardinality q form
the q-th term.
-/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]

abbrev PolynomialCechFamily := (s : Finset σ) → LaurentMonomials.ProjectiveCech.ChartLocalization R s

def polynomialCechDifferential :
    PolynomialCechFamily (σ := σ) R →ₗ[R] PolynomialCechFamily (σ := σ) R where
  toFun f s := ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i •
    LaurentRestriction.ProjectiveCech.chartRestriction R (Finset.erase_subset i s) (f (s.erase i))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm r]

theorem polynomialCechDifferential_coordinates (f : PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) :
    LaurentCoordinates.ProjectiveCech.chartCoordinates R s (polynomialCechDifferential R f s) a =
      Cech.Contraction.ProjectiveCech.cechDifferential R (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) s := by
  change LaurentCoordinates.ProjectiveCech.chartCoordinates R s (∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i •
    LaurentRestriction.ProjectiveCech.chartRestriction R (Finset.erase_subset i s) (f (s.erase i))) a = _
  simp only [map_sum, map_smul, LaurentCoordinates.ProjectiveCech.chartCoordinates_restriction, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Cech.Contraction.ProjectiveCech.cechDifferential]

theorem polynomialCechDifferential_square (f : PolynomialCechFamily (σ := σ) R) :
    polynomialCechDifferential R (polynomialCechDifferential R f) = 0 := by
  funext s
  apply LaurentCoordinates.ProjectiveCech.chartCoordinates_injective R s
  ext a
  rw [polynomialCechDifferential_coordinates]
  have he : (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (polynomialCechDifferential R f t) a) =
      Cech.Contraction.ProjectiveCech.cechDifferential R (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) := by
    funext t
    exact polynomialCechDifferential_coordinates R f t a
  rw [he, Cech.Differential.ProjectiveCech.cechDifferential_square, Pi.zero_apply, Pi.zero_apply, map_zero,
    Finsupp.zero_apply]

def CechHomogeneous (d : ℤ) (f : PolynomialCechFamily (σ := σ) R) : Prop :=
  ∀ s, f s ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s d

def CechCardSupported (q : ℕ) (f : PolynomialCechFamily (σ := σ) R) : Prop :=
  ∀ s, s.card ≠ q → f s = 0

theorem polynomialCechDifferential_homogeneous (d : ℤ) (f : PolynomialCechFamily (σ := σ) R)
    (hf : CechHomogeneous R d f) : CechHomogeneous R d (polynomialCechDifferential R f) := by
  intro s
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (LaurentDegree.ProjectiveCech.chartRestriction_preserves_degree R (Finset.erase_subset i s) d _ (hf _))

theorem polynomialCechDifferential_card (q : ℕ) (f : PolynomialCechFamily (σ := σ) R)
    (hf : CechCardSupported R q f) : CechCardSupported R (q + 1) (polynomialCechDifferential R f) := by
  intro s hs
  apply LaurentCoordinates.ProjectiveCech.chartCoordinates_injective R s
  ext a
  rw [polynomialCechDifferential_coordinates, map_zero, Finsupp.zero_apply]
  apply Cech.Differential.ProjectiveCech.cechDifferential_card_support R q _ ?_ s hs
  intro t ht
  rw [hf t ht, map_zero, Finsupp.zero_apply]

omit [LinearOrder σ] in
theorem polynomialCech_bounded (q : ℕ) (hq : Fintype.card σ < q)
    (f : PolynomialCechFamily (σ := σ) R) (hf : CechCardSupported R q f) : f = 0 := by
  funext s
  apply hf s
  exact ne_of_lt ((Finset.card_le_univ s).trans_lt hq)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Cech.ProjectiveCech
