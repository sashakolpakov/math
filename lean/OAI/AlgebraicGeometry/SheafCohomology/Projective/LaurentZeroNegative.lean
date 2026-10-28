import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport

/-! # Laurent Zero Negative -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroNegative

noncomputable section

/-! Negative projective twists have no degree-zero Čech cohomology in positive dimension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport
universe u
namespace MvPolynomial
open _root_.MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ] [Nontrivial σ]

theorem laurentZeroCycleWeight_eq_zero_of_nonempty_support (d : ℤ)
    (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d)
    (he : (e.liftedNegativeSupport : Set (ULift.{u} σ)) ≠ ∅)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) :
    LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e z = 0 := by
  apply Subtype.ext
  by_cases hu : (e.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ
  · have hz (N : Set (ULift.{u} σ)) (hN : N = Set.univ)
        (s : OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of R), ⊤) N 0) : s = 0 := by
      subst N
      exact OrderedCechSupport.orderedCechFullSupport_eq_zero_of_card_ne Γ(Spec (CommRingCat.of R), ⊤) 0
        (by have := Fintype.one_lt_card (α := ULift.{u} σ); omega) s
    exact hz e.liftedNegativeSupport hu (LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e z).val
  · obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem e.liftedNegativeSupport).mp hu
    apply OrderedCechSupportContraction.orderedCechSupportDifferential_zero_injective Γ(Spec (CommRingCat.of R), ⊤)
      e.liftedNegativeSupport (Set.nonempty_iff_ne_empty.mpr he) i hi
    exact (LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e z).property.trans (map_zero _).symm

omit [LinearOrder σ] [Nontrivial σ] in
theorem homogeneousLaurentExponent_support_nonempty_of_neg {d : ℤ}
    (hd : d < 0) (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
    (e.liftedNegativeSupport : Set (ULift.{u} σ)) ≠ ∅ := by
  intro he
  have hnonneg (i : σ) : 0 ≤ e.val i := by
    by_contra h
    have hm : ULift.up i ∈ e.liftedNegativeSupport := lt_of_not_ge h
    rw [he] at hm
    exact hm
  have hdeg : 0 ≤ Finsupp.degree e.val := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
  rw [e.property] at hdeg
  omega

theorem laurentZeroCycles_subsingleton_of_neg (d : ℤ) (hd : d < 0) :
    Subsingleton (LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) := by
  have hz (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) : z = 0 := by
    apply LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycle_ext d
    intro e
    rw [map_zero]
    exact laurentZeroCycleWeight_eq_zero_of_nonempty_support d e
      (homogeneousLaurentExponent_support_nonempty_of_neg hd e) z
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem homogeneousLaurentHZero_subsingleton_of_neg (j : σ) (d : ℤ) (hd : d < 0) :
    Subsingleton ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology 0) := by
  have := laurentZeroCycles_subsingleton_of_neg (R := R) (σ := σ) d hd
  exact (DegreeZeroPolynomials.MvPolynomial.homogeneousLaurentHZeroLinearEquivCycles (R := R) j d).injective.subsingleton

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroNegative
