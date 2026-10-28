import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerHilbertDegreeBound
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicFinrank

/-! # Module Hilbert Degree Bound -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHilbertDegreeBound

noncomputable section

/-! Ambient degree bounds for Hilbert polynomials of finite graded polynomial modules.

Noetherian induction adjoins one homogeneous element at a time. The resulting
cyclic quotient is a shifted homogeneous coordinate quotient, and the exact
sequence on degree pieces adds its Hilbert polynomial.
-/

open _root_.MvPolynomial
universe u

variable {K : Type u} [Field K] {r : ℕ}

theorem finiteGradedModule_quotient_eventuallyPolynomialOfDegree
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (r + 1)) K)
    (P : Submodule (MvPolynomial (Fin (r + 1)) K) D.Carrier)
    (hP : P.IsHomogeneous D.grading) :
    BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
      (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient D.grading P (n : ℤ)) : ℚ)) r := by
  have (d : ℤ) : Module.Finite K (D.grading d) :=
    GradedPieceFiniteness.finiteGradedPolynomialModule_piece_finite K D d
  induction P using IsNoetherian.induction with
  | hgt P ih =>
    by_cases ht : P = ⊤
    · subst P
      refine ⟨0, by simp, 0, fun n _ => ?_⟩
      change (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient D.grading ⊤ (n : ℤ)) : ℚ) = _
      have hrel : GradedCyclicDegreeSequence.degreeRelations D.grading
          (⊤ : Submodule (MvPolynomial (Fin (r + 1)) K) D.Carrier) (n : ℤ) = ⊤ := by
        ext x
        simp [GradedCyclicDegreeSequence.degreeRelations]
      unfold GradedCyclicDegreeSequence.DegreeQuotient
      rw [hrel, Module.finrank_zero_of_subsingleton]
      simp
    · obtain ⟨m, e, hm, hnot⟩ := GradedCyclicSubmodule.exists_homogeneous_not_mem D.grading ht
      let Q := P ⊔ Submodule.span (MvPolynomial (Fin (r + 1)) K) {m}
      have hPQ : P < Q := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hnot
        rw [heq]
        exact (show Submodule.span (MvPolynomial (Fin (r + 1)) K) {m} ≤ Q from le_sup_right)
          (Submodule.mem_span_singleton_self m)
      have hQ : Q.IsHomogeneous D.grading :=
        GradedCyclicSubmodule.sup_isHomogeneous D.grading hP
          (GradedCyclicSubmodule.span_singleton_isHomogeneous (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) D.grading hm)
      have hc := IntegerHilbertDegreeBound.integerIdealDegree_eventuallyPolynomialOfDegree (GradedCyclicSubmodule.relativeAnnihilator P m)
        (GradedCyclicSubmodule.relativeAnnihilator_isHomogeneous (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) D.grading P hP hm) e
      obtain ⟨F, hF, b, hb⟩ := (ih Q hPQ hQ).add hc
      refine ⟨F, hF, b, fun n hn => ?_⟩
      change (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient D.grading P (n : ℤ)) : ℚ) = F.eval (n : ℚ)
      rw [GradedCyclicFinrank.cyclicDegreeSequence_finrank (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) D.grading P hP hm]
      exact hb n hn

theorem finiteGradedPolynomialModule_eventuallyPolynomialOfDegree
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (r + 1)) K) :
    BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n => (Module.finrank K (D.grading (n : ℤ)) : ℚ)) r := by
  have hbot : (⊥ : Submodule (MvPolynomial (Fin (r + 1)) K) D.Carrier).IsHomogeneous
      D.grading := by
    intro d m hm
    change m = 0 at hm
    subst m
    simp
  obtain ⟨F, hF, b, hb⟩ := finiteGradedModule_quotient_eventuallyPolynomialOfDegree D ⊥ hbot
  refine ⟨F, hF, b, fun n hn => ?_⟩
  have hrel : GradedCyclicDegreeSequence.degreeRelations D.grading
      (⊥ : Submodule (MvPolynomial (Fin (r + 1)) K) D.Carrier) (n : ℤ) = ⊥ := by
    ext x
    simp [GradedCyclicDegreeSequence.degreeRelations]
  have hd := ((GradedCyclicDegreeSequence.degreeRelations D.grading
      (⊥ : Submodule (MvPolynomial (Fin (r + 1)) K) D.Carrier) (n : ℤ)).quotEquivOfEqBot hrel).finrank_eq
  change (Module.finrank K (D.grading (n : ℤ)) : ℚ) = F.eval (n : ℚ)
  rw [← hd]
  exact hb n hn

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleHilbertDegreeBound
