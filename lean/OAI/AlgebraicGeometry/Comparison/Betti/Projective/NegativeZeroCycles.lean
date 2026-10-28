import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCycleModel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport

/-! # Negative Zero Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeZeroCycles.Dolbeault

noncomputable section

/-! Original algebraic Laurent zero cycles vanish for negative twists in positive projective dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport

theorem projectiveLaurentZeroWeight_zero_nonempty (n : ℕ) (d : ℤ)
    (e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n + 2)) d)
    (he : (e.liftedNegativeSupport : Set (ULift.{0} (Fin (n + 2)))) ≠ ∅)
    (z : SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 2)) d) :
    SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := ℂ) d e z = 0 := by
  apply Subtype.ext
  by_cases hu : (e.liftedNegativeSupport : Set (ULift.{0} (Fin (n + 2)))) = Set.univ
  · have hz (N : Set (ULift.{0} (Fin (n + 2)))) (hN : N = Set.univ)
        (s : SheafCohomology.Projective.OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of ℂ), ⊤) N 0) : s = 0 := by
      subst N
      exact SheafCohomology.Projective.OrderedCechSupport.orderedCechFullSupport_eq_zero_of_card_ne Γ(Spec (CommRingCat.of ℂ), ⊤) 0 (by simp) s
    exact hz e.liftedNegativeSupport hu (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := ℂ) d e z).val
  · obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem e.liftedNegativeSupport).mp hu
    apply SheafCohomology.Projective.OrderedCechSupportContraction.orderedCechSupportDifferential_zero_injective Γ(Spec (CommRingCat.of ℂ), ⊤)
      e.liftedNegativeSupport (Set.nonempty_iff_ne_empty.mpr he) i hi
    exact (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := ℂ) d e z).property.trans (map_zero _).symm

theorem projectiveNegativeLaurentWeight_support_nonempty (n : ℕ) (d : ℤ) (hd : d < 0)
    (e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (n + 2)) d) :
    (e.liftedNegativeSupport : Set (ULift.{0} (Fin (n + 2)))) ≠ ∅ := by
  intro he
  have hn (i : Fin (n + 2)) : 0 ≤ e.val i := by
    by_contra hi
    have hm : (ULift.up i : ULift.{0} (Fin (n + 2))) ∈ e.liftedNegativeSupport := lt_of_not_ge hi
    rw [he] at hm
    exact hm
  have hdeg : 0 ≤ Finsupp.degree e.val := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_nonneg (fun i _ => hn i)
  rw [e.property] at hdeg
  omega

theorem projectiveLaurentZeroCycles_subsingleton_neg (n : ℕ) (d : ℤ) (hd : d < 0) :
    Subsingleton (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 2)) d) := by
  have hz (z : SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 2)) d) : z = 0 := by
    apply SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycle_ext d
    intro e
    rw [map_zero]
    exact projectiveLaurentZeroWeight_zero_nonempty n d e
      (projectiveNegativeLaurentWeight_support_nonempty n d hd e) z
  exact ⟨fun z w => (hz z).trans (hz w).symm⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeZeroCycles.Dolbeault
