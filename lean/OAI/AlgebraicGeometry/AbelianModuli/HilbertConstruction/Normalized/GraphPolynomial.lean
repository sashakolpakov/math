import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EulerNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.PolynomialPowers

/-! # Graph Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical graph bundle has its polarization-type Hilbert polynomial
on every field fiber. The section formula holds in every positive degree. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u

/-- The section polynomial of the canonical graph bundle for type `δ`. -/
def Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial (g : ℕ) (δ : Fin g → ℕ) : Polynomial ℚ :=
  Polynomial.monomial g (((2 : ℕ) ^ g * ∏ i, δ i : ℕ) : ℚ)

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_normalized_hilbertPolynomial_overField
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    A.graphBundle.HasSectionHilbertPolynomial A.abelian.scheme.hom
      (Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ) := by
  have h := A.graphBundle_monomial_hilbertPolynomial_overField hN hNk
  rw [A.graphBundle_euler_normalized_overField hg hN hNk] at h
  simpa only [Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_hilbertPolynomial_eq_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (P : Polynomial ℚ)
    (hP : A.graphBundle.HasSectionHilbertPolynomial A.abelian.scheme.hom P) :
    P = Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ :=
  A.graphBundle.sectionHilbertPolynomial_unique A.abelian.scheme.hom hP
    (A.graphBundle_normalized_hilbertPolynomial_overField hg hN hNk)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_sections_finrank_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (m : ℕ) (hm : 0 < m) :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      (A.graphBundle.tensorPower m).sheaf) = (2 : ℕ) ^ g * (∏ i, δ i) * m ^ g := by
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  have he := A.graphBundle_tensorPower_euler_normalized_overField hg hN hNk m
  have hs := A.graphBundle_positivePower_euler_eq_sections hN hunit m hm
  apply Nat.cast_injective (R := ℤ)
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hs.symm.trans he

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_normalized_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (m : ℕ) (hm : 0 < m) :
    (A.graphBundle.tensorPower m).HasSectionHilbertPolynomial A.abelian.scheme.hom
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
        (Polynomial.C (m : ℚ) * Polynomial.X)) :=
  (A.graphBundle_normalized_hilbertPolynomial_overField hg hN hNk).tensorPower m hm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
