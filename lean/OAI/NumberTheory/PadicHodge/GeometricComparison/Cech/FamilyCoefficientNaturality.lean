import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Family Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyCoefficientNaturality.CechFamilyRefinement

noncomputable section

/-! The actual coefficient-change comparison commutes with actual Čech cover refinement. -/

open _root_.CategoryTheory Limits Opposite Simplicial

universe w v u vA uA vB uB

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w, w} G]
  (U V : FormalCoproduct.{w} C) (r : V ⟶ U) (P : Cᵒᵖ ⥤ A)

theorem coefficient_naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (FamilyRefinement.CechFamilyRefinement.map U V r P) ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G V.cech P).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G U.cech P).hom ≫ FamilyRefinement.CechFamilyRefinement.map U V r (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f]
  let E := U.cech.obj (op ⦋n⦌)
  let D := V.cech.obj (op ⦋n⦌)
  let a : D ⟶ E := (FormalCoproduct.cechFunctor.map r).app (op ⦋n⦌)
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G
    (fun i : E.I => P.obj (op (E.obj i))) (fun i : D.I => P.obj (op (D.obj i))) a.f
    (fun i => P.map (a.φ i).op)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyCoefficientNaturality.CechFamilyRefinement
