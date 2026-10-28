import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPolynomial

/-! # Normalized Graph Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The type polynomial and every positive-degree section dimension are
uniform on all field-valued points of any tame base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u

theorem Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit
    {S : Scheme.{u}} {N : ℕ} (hN : IsUnit (N : Γ(S, ⊤)))
    {K : Type u} [Field K] (f : Spec (.of K) ⟶ S) : (N : K) ≠ 0 := by
  let φ : Γ(S, ⊤) →+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp f.appTop.hom
  have hu : IsUnit (N : K) := by simpa only [map_natCast] using hN.map φ
  exact isUnit_iff_ne_zero.mp hu

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackGraphBundle_normalized_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hNunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    (A.pullback f).graphBundle.HasSectionHilbertPolynomial
      (A.pullback f).abelian.scheme.hom (Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ) :=
  (A.pullback f).graphBundle_normalized_hilbertPolynomial_overField hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hNunit f)

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackGraphBundle_positivePower_sections_finrank
    (hg : 0 < g) (hN : 3 ≤ N) (hNunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) (m : ℕ) (hm : 0 < m) :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (A.pullback f).abelian.scheme.hom).obj
      ((A.pullback f).graphBundle.tensorPower m).sheaf) =
        (2 : ℕ) ^ g * (∏ i, δ i) * m ^ g :=
  (A.pullback f).graphBundle_positivePower_sections_finrank_normalized hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hNunit f) m hm

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackGraphBundle_positivePower_normalized_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hNunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) (m : ℕ) (hm : 0 < m) :
    ((A.pullback f).graphBundle.tensorPower m).HasSectionHilbertPolynomial
      (A.pullback f).abelian.scheme.hom
        ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
          (Polynomial.C (m : ℚ) * Polynomial.X)) :=
  (A.pullback f).graphBundle_positivePower_normalized_hilbertPolynomial hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hNunit f) m hm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
