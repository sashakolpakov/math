import OAI.AlgebraicGeometry.SheafCohomology.Projective.Euler

/-! # Euler Range -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.EulerRange

noncomputable section

open _root_.MvPolynomial

/-! The projective Euler sum is independent of an increased cutoff. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {r : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveSheafEuler_eq_sum_range
    (M : (Proj (homogeneousSubmodule (Fin (r + 1)) R)).Modules)
    (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) (b : ℕ) (hb : r + 1 ≤ b) :
    Euler.MvPolynomial.projectiveSheafEuler M = ∑ q ∈ Finset.range b, (-1 : ℤ) ^ q *
      (Module.finrank Γ(Spec (CommRingCat.of R), ⊤)
        ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1))) M
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1)))).homology q) : ℤ) := by
  let := hfield.toField
  apply Finset.sum_subset (Finset.range_mono hb)
  intro q _ hq
  let K := OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1))) M
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1)))
  have hX : IsZero (K.X q) :=
    OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (r + 1))) M
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (r + 1))) q
      (by simpa only [Fintype.card_ulift, Fintype.card_fin, Finset.mem_range, not_lt] using hq)
  let : Subsingleton (K.homology q) := ModuleCat.subsingleton_of_isZero
    (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc q) hX)
  change (-1 : ℤ) ^ q * (Module.finrank Γ(Spec (CommRingCat.of R), ⊤) (K.homology q) : ℤ) = 0
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.EulerRange
