import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import Mathlib.Algebra.Homology.HomologicalComplex

/-! # Truncation Map Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationMapZero.HodgeTruncationMapZero

noncomputable section

/-! Vanishing in positive form degrees kills the original Hodge
truncation map, also after an actual coefficient functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem rightZero {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (h : b = 0) : a ≫ b = 0 := by
  rw [h, comp_zero]

private theorem leftZero {C : Type*} [Category* C] [HasZeroMorphisms C]
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (h : a = 0) : a ≫ b = 0 := by
  rw [h, zero_comp]

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]
  {K : CochainComplex C ℕ} {L M : CochainComplex D ℕ}

theorem mapped (a : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) (r : ℤ)
    (h : ∀ n : ℕ, r ≤ (n : ℤ) → a.f n = 0) :
    (F.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) ≫ a = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change F.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) ≫ a.f n = 0
  by_cases hn : r ≤ (n : ℤ)
  · exact rightZero (F.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n)) (a.f n) (h n hn)
  · have he : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n = 0 := by
      simp only [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right hn]
    exact leftZero (F.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n)) (a.f n)
      ((congrArg F.map he).trans (F.map_zero _ _))

theorem after_map (a : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) (b : L ⟶ M) (r : ℤ)
    (h : ∀ n : ℕ, r ≤ (n : ℤ) → b.f n = 0) :
    (F.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) ≫ a ≫ b = 0 := by
  apply mapped F (a ≫ b) r
  intro n hn
  change a.f n ≫ b.f n = 0
  rw [h n hn, comp_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationMapZero.HodgeTruncationMapZero
