import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.SectionDimensionFieldExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.EulerFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Field Euler Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The exact Euler monomial and positive original coefficient descend from an algebraic closure to every ground field through actual section base change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_euler_fieldExtension {F : Type u} [Field F]
    (φ : CommRingCat.of K ⟶ CommRingCat.of F)
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤))) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.pullback (Spec.map φ)).abelian.scheme.hom
        (A.pullback (Spec.map φ)).graphBundle.sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf := by
  have h := A.graphBundle_positivePower_euler_fieldExtension φ hN hunit 1 Nat.zero_lt_one
  have hA := Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.abelian.scheme.hom
    A.graphBundle.tensorPowerOneIso
  have hB := Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso
    (A.pullback (Spec.map φ)).abelian.scheme.hom
    (A.pullback (Spec.map φ)).graphBundle.tensorPowerOneIso
  exact hB.symm.trans (h.trans hA)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_euler_overField
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (m : ℕ) (hm : 0 < m) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf * (m : ℤ) ^ g := by
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let B := A.pullback (Spec.map φ)
  have hNF : (N : AlgebraicClosure K) ≠ 0 := by
    intro hz
    apply hNk
    apply (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_natCast, map_zero] using hz
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  calc
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic B.abelian.scheme.hom (B.graphBundle.tensorPower m).sheaf :=
      (A.graphBundle_positivePower_euler_fieldExtension φ hN hunit m hm).symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic B.abelian.scheme.hom B.graphBundle.sheaf * (m : ℤ) ^ g :=
      B.graphBundle_tensorPower_euler hN hNF m
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf * (m : ℤ) ^ g :=
      congrArg (fun z : ℤ => z * (m : ℤ) ^ g) (A.graphBundle_euler_fieldExtension φ hN hunit)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_tensorPower_euler_overField
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf * (m : ℤ) ^ g := by
  obtain ⟨P, hP⟩ := A.graphBundle_eulerPolynomial_exists_overField
  let Q := Polynomial.monomial g
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ)
  have he : P = Q := HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals P Q (by
    intro n hn
    have h := congrArg (fun z : ℤ => (z : ℚ))
      (A.graphBundle_positivePower_euler_overField hN hNk n hn)
    rw [hP n]
    simpa only [Q, Polynomial.eval_monomial, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast] using h)
  have h := (hP m).symm
  rw [he, Polynomial.eval_monomial] at h
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
