import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentComplex

/-! # Laurent Homology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentHomology.Dolbeault

noncomputable section

/-! The Laurent-model comparison computes the same original analytification map on cohomology. -/

open _root_.CategoryTheory _root_.HomologicalComplex

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveLaurentOriginalComparison_homotopy (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    Homotopy ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).hom ≫ LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d)
      (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d) := by
  let e := LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d
  let f := ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d
  change Homotopy (e.hom ≫ (e.inv ≫ f)) f
  exact (Homotopy.ofEq (Category.assoc e.hom e.inv f).symm).trans
    ((e.homotopyHomInvId.compRight f).trans (Homotopy.ofEq (Category.id_comp f)))

theorem projectiveLaurentOriginalComparison_homologyMap (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (r : ℕ) :
    homologyMap (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).hom r ≫
      homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d) r =
        homologyMap (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d) r :=
  (homologyMap_comp _ _ r).symm.trans
    ((projectiveLaurentOriginalComparison_homotopy n j d).homologyMap_eq r)

theorem projectiveOriginalComparison_isIso_of_laurent (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (r : ℕ)
    [IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d) r)] :
    IsIso (homologyMap (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d) r) := by
  let e := (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).toHomologyIso r
  let : IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).hom r) :=
    inferInstanceAs (IsIso e.hom)
  have h : IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentHomotopyEquiv n j d).hom r ≫
      homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d) r) := inferInstance
  rw [projectiveLaurentOriginalComparison_homologyMap] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentHomology.Dolbeault
