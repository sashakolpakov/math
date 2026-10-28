import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport

/-! # Negative Laurent Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NegativeLaurentSections

noncomputable section

/-! Negative-degree homogeneous Laurent zero cycles vanish when
projective space has at least two coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ] [Nontrivial σ]

omit [LinearOrder σ] [Nontrivial σ] in
theorem negativeLaurentWeight_support_nonempty {d : ℤ} (hd : d < 0) (e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
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

theorem negativeLaurentZeroCycleWeight_zero (d : ℤ) (hd : d < 0)
    (e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) (z : SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) :
    SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e z = 0 := by
  apply Subtype.ext
  by_cases hu : (e.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ
  · have hz (N : Set (ULift.{u} σ)) (hN : N = Set.univ)
        (s : SheafCohomology.Projective.OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (.of R), ⊤) N 0) : s = 0 := by
      subst N
      exact SheafCohomology.Projective.OrderedCechSupport.orderedCechFullSupport_eq_zero_of_card_ne Γ(Spec (.of R), ⊤) 0
        (by have := Fintype.one_lt_card (α := ULift.{u} σ); omega) s
    exact hz e.liftedNegativeSupport hu (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e z).val
  · obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem e.liftedNegativeSupport).mp hu
    apply SheafCohomology.Projective.OrderedCechSupportContraction.orderedCechSupportDifferential_zero_injective Γ(Spec (.of R), ⊤)
      e.liftedNegativeSupport (Set.nonempty_iff_ne_empty.mpr (negativeLaurentWeight_support_nonempty hd e)) i hi
    exact (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) d e z).property.trans (map_zero _).symm

theorem negativeLaurentZeroCycles_subsingleton (d : ℤ) (hd : d < 0) :
    Subsingleton (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) := by
  have hz (z : SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d) : z = 0 := by
    apply SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycle_ext d
    intro e
    rw [map_zero]
    exact negativeLaurentZeroCycleWeight_zero d hd e z
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NegativeLaurentSections
