import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor

/-! # Total Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientCoordinates

noncomputable section

/-! The canonical coefficient isomorphism on the actual finite total
has the expected formula on each original summand. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteCoproducts D]
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

local instance : K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance : (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

theorem injection (p q n : ℕ) (h : p+q=n) :
    F.map (K.ιTotal (.up ℕ) p q n h) ≫
      (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv.f n =
        (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) p q n h := by
  have hi : (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) p q n h ≫
      (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).hom.f n = F.map (K.ιTotal (.up ℕ) p q n h) :=
    AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent F K p q n h
  calc
    _ = ((AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) p q n h ≫
        (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).hom.f n) ≫
          (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv.f n := congrArg (· ≫ _) hi.symm
    _ = _ := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id]
      exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientCoordinates
