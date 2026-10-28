import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdditionGraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphBundleBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FieldSectionPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Addition Graph Field Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The addition-graph section Hilbert polynomial descends from an
algebraic closure to every field, and hence applies at every field-valued
point of an arbitrary tame base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_hilbertPolynomial_overField
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    A.additionGraphBundle.HasSectionHilbertPolynomial (A.abelian.scheme ⊗ A.abelian.scheme).hom
      (AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ) := by
  let : IsProper (A.abelian.scheme ⊗ A.abelian.scheme).hom := inferInstanceAs
    (IsProper (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫
      A.abelian.scheme.hom))
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let B := A.pullback (Spec.map φ)
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  exact (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_cartesianFieldExtension φ
    (Graph.FamilyNaturality.overProductBaseChange_isPullback (Spec.map φ) A.abelian.scheme A.abelian.scheme)
    A.additionGraphBundle B.additionGraphBundle (A.additionGraphBundle_baseChangeIso (Spec.map φ)) _).mpr
      (A.pulledBackAdditionGraphBundle_hilbertPolynomial hg hN hunit (AlgebraicClosure K) (Spec.map φ))

theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_positivePower_hilbertPolynomial_overField
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (d : ℕ) (hd : 0 < d) :
    (A.additionGraphBundle.tensorPower d).HasSectionHilbertPolynomial
      (A.abelian.scheme ⊗ A.abelian.scheme).hom
      ((AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp (Polynomial.C (d : ℚ) * Polynomial.X)) :=
  (A.additionGraphBundle_hilbertPolynomial_overField hg hN hNk).tensorPower d hd

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackAdditionGraphBundle_hilbertPolynomial_allFields
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    let B := A.pullback f
    B.additionGraphBundle.HasSectionHilbertPolynomial (B.abelian.scheme ⊗ B.abelian.scheme).hom
      (AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ) :=
  (A.pullback f).additionGraphBundle_hilbertPolynomial_overField hg hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f)

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackAdditionGraphBundle_positivePower_hilbertPolynomial_allFields
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) (d : ℕ) (hd : 0 < d) :
    let B := A.pullback f
    (B.additionGraphBundle.tensorPower d).HasSectionHilbertPolynomial
      (B.abelian.scheme ⊗ B.abelian.scheme).hom
      ((AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp (Polynomial.C (d : ℚ) * Polynomial.X)) :=
  (A.pulledBackAdditionGraphBundle_hilbertPolynomial_allFields hg hN hunit K f).tensorPower d hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
