import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Top Restriction Coefficients -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionCoefficients.CechTopRestrictionCoefficients

noncomputable section

/-! Product-preserving coefficient change respects top-section restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u a b v z w
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type v} [Category.{z} B] [Preadditive B] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w, w} G]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

theorem map : G.map (TopRestriction.CechTopRestriction.map C U P) ≫
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P).hom.f 0 =
      TopRestriction.CechTopRestriction.map C U (P ⋙ G) := by
  change G.map (Pi.lift (fun t : Fin 1 → ι => P.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤)).op)) ≫
    (𝟙 _ ≫ piComparison G (fun t : Fin 1 → ι => P.obj (op (∏ᶜ (U ∘ t))))) =
      Pi.lift (fun t : Fin 1 → ι => G.map (P.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤)).op))
  rw [Category.id_comp]
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π, ← G.map_comp]

def initialIso : (TopRestriction.CechTopRestriction.initial C U P).map G ≅
    TopRestriction.CechTopRestriction.initial C U (P ⋙ G) :=
  ShortComplex.isoMk (Iso.refl _)
    ((HomologicalComplex.eval B (.up ℕ) 0).mapIso
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P))
    ((HomologicalComplex.eval B (.up ℕ) 1).mapIso
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P))
    ((Category.id_comp _).trans (CechTopRestrictionCoefficients.map C G U P).symm)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P).hom.comm 0 1)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionCoefficients.CechTopRestrictionCoefficients
