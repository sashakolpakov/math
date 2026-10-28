import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension

/-! # Line Parameter -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LineParameter

noncomputable section

section

/-! Ratios of homogeneous coordinates give actual rational
functions, and their regular stalk representatives agree with them. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace RationalFractions

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets.StalkFractions

instance integral (n : ℕ) : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :=
  Dimension.projective_integral n

def coordinate (n : ℕ) (i : Fin (n + 1)) : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 :=
  ⟨MvPolynomial.X i, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i⟩

theorem generic_coordinate (n : ℕ) (i : Fin (n + 1)) :
    (coordinate n i).val ∉ (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)).asHomogeneousIdeal := by
  have hn : Nonempty (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :=
    ⟨(Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv
      (genericPoint (Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))))⟩
  exact ((genericPoint_spec (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)).mem_open_set_iff
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).isOpen).mpr ⟨hn.some.val, trivial, hn.some.property⟩

def ratio (n : ℕ) (i j : Fin (n + 1)) : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).functionField :=
  PointJets.StalkFractions.fraction n (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (coordinate n i) (coordinate n j)
    (generic_coordinate n j)

theorem fraction_field (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ x.asHomogeneousIdeal)
    (hη : s.val ∉ (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)).asHomogeneousIdeal) :
    algebraMap ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.stalk x) (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).functionField
      (PointJets.StalkFractions.fraction n x a s hs) = PointJets.StalkFractions.fraction n (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) a s hη := by
  rw [← PointJets.StalkFractions.germ n x a s hs, ← PointJets.StalkFractions.germ n (genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) a s hη]
  change ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.germ _ x hs ≫
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.stalkSpecializes
      ((genericPoint_spec (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)).specializes trivial)) _ = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem ratio_mul_reverse (n : ℕ) (i j : Fin (n + 1)) :
    ratio n i j * ratio n j i = 1 := by
  unfold ratio
  rw [PointJets.StalkFractions.mul, PointJets.StalkFractions.self]

theorem ratio_reverse (n : ℕ) (i j : Fin (n + 1)) : ratio n j i = (ratio n i j)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (ratio_mul_reverse n i j)).symm

end RationalFractions

end

/-! The standard projective-line coordinate and its inverse are
regular on the two coordinate charts. Dominant pullback gives the
same two-chart condition on any integral parameter scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LineParameter.RationalFractions OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets.StalkFractions

def coordinate : (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).functionField := RationalFractions.ratio 1 1 0

theorem charts (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) :
    (∃ u : (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).presheaf.stalk x,
      algebraMap ((Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).presheaf.stalk x) (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).functionField u = coordinate) ∨
    (∃ u : (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).presheaf.stalk x,
      algebraMap ((Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).presheaf.stalk x) (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).functionField u = coordinate⁻¹) := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen 1 x
  fin_cases i
  · exact Or.inl ⟨PointJets.StalkFractions.fraction 1 x (RationalFractions.coordinate 1 1)
      (RationalFractions.coordinate 1 0) hi,
      RationalFractions.fraction_field 1 x (RationalFractions.coordinate 1 1)
        (RationalFractions.coordinate 1 0) hi (RationalFractions.generic_coordinate 1 0)⟩
  · refine Or.inr ⟨PointJets.StalkFractions.fraction 1 x (RationalFractions.coordinate 1 0)
      (RationalFractions.coordinate 1 1) hi, ?_⟩
    exact (RationalFractions.fraction_field 1 x (RationalFractions.coordinate 1 0)
      (RationalFractions.coordinate 1 1) hi (RationalFractions.generic_coordinate 1 1)).trans
        (RationalFractions.ratio_reverse 1 1 0)

variable {Z : Scheme} [IsIntegral Z] (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hη : f (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

def pullback : Z.functionField := Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη coordinate

theorem pullback_charts (x : Z) :
    (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = pullback f hη) ∨
    (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = (pullback f hη)⁻¹) := by
  rcases charts (f x) with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact Or.inl ⟨f.stalkMap x u,
      (Divisor.DivisorRestriction.genericFieldMap_stalk f hη x u).symm.trans
        (congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) hu)⟩
  · refine Or.inr ⟨f.stalkMap x u, ?_⟩
    rw [← Divisor.DivisorRestriction.genericFieldMap_stalk f hη x u, hu]
    exact map_inv₀ (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom coordinate

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LineParameter
