import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.GraphPresentationTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.EulerSectionPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.AdditionEuler

/-! # Addition Graph Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual addition-graph line bundle is ample. Its Euler formula
therefore gives a uniform section Hilbert polynomial on every geometric
fiber, including every positive tensor power. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u

def AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial (g : ℕ) (δ : Fin g → ℕ) : Polynomial ℚ :=
  Polynomial.monomial (2 * g) (((3 : ℕ) ^ g * ((2 : ℕ) ^ g * ∏ i, δ i) ^ 2 : ℕ) : ℚ)

section Field
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_isAmple : A.additionGraphBundle.IsAmple := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_overField.exists_powerProjectiveEmbedding A.abelian.scheme.hom
  exact E.binaryGraphBundle_isAmple μ[A.abelian.scheme]

theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_hilbertPolynomial_of_formula
    (L : Line.Bundles.LineBundle A.abelian.scheme.left)
    (e : (((A.dual.poincareAt A.polarization.isogeny.hom).tensor
      (L.pullback (CategoryTheory.CartesianMonoidalCategory.fst A.abelian.scheme A.abelian.scheme).left)).tensor
        (L.pullback (CategoryTheory.CartesianMonoidalCategory.snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
      (L.pullback μ[A.abelian.scheme].left).sheaf)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    A.additionGraphBundle.HasSectionHilbertPolynomial (A.abelian.scheme ⊗ A.abelian.scheme).hom
      (AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ) := by
  let : IsProper (A.abelian.scheme ⊗ A.abelian.scheme).hom := inferInstanceAs
    (IsProper (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫
      A.abelian.scheme.hom))
  apply Line.Bundles.LineBundle.hasSectionHilbertPolynomial_of_euler _ A.additionGraphBundle A.additionGraphBundle_isAmple
  intro n
  rw [AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial, Polynomial.eval_monomial]
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (A.additionGraphBundle_tensorPower_euler_normalized L e hg hN hNk n)
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h.symm

end Field

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackAdditionGraphBundle_hilbertPolynomial
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) :
    let B := A.pullback f
    B.additionGraphBundle.HasSectionHilbertPolynomial (B.abelian.scheme ⊗ B.abelian.scheme).hom
      (AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ) := by
  obtain ⟨L, ⟨e⟩⟩ := (Geometric.AdditionEuler.PolarizedAbelianWithLevel.geometricPullback_normalizedPolarizationFormula A) K f
  exact (A.pullback f).additionGraphBundle_hilbertPolynomial_of_formula L e hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f)

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackAdditionGraphBundle_positivePower_hilbertPolynomial
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S) (d : ℕ) (hd : 0 < d) :
    let B := A.pullback f
    (B.additionGraphBundle.tensorPower d).HasSectionHilbertPolynomial (B.abelian.scheme ⊗ B.abelian.scheme).hom
      ((AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp (Polynomial.C (d : ℚ) * Polynomial.X)) :=
  (A.pulledBackAdditionGraphBundle_hilbertPolynomial hg hN hunit K f).tensorPower d hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
