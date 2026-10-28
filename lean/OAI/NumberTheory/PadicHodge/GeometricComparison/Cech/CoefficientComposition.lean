import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Coefficient Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CoefficientComposition.CechCoefficientComposition

noncomputable section

/-! The canonical Čech coefficient comparison respects composition of product-preserving additive functors. -/

open _root_.CategoryTheory Limits Opposite Simplicial

universe w v u vA uA vB uB vD uD

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasProducts.{w} D]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
  [PreservesLimitsOfSize.{w, w} F] [PreservesLimitsOfSize.{w, w} G]

omit [Preadditive A] [Preadditive B] [Preadditive D] [F.Additive] [G.Additive]
  [PreservesLimitsOfSize.{w, w} F] [PreservesLimitsOfSize.{w, w} G] in
theorem piComparison {ι : Type w} (P : ι → A) :
    G.map (Limits.piComparison F P) ≫ Limits.piComparison G (fun i => F.obj (P i)) =
      Limits.piComparison (F ⋙ G) P := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp, piComparison_comp_π]
  exact (piComparison_comp_π (F ⋙ G) P i).symm

theorem hom (E : SimplicialObject (FormalCoproduct.{w} C)) (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso F E P).hom ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G E (P ⋙ F)).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso (F ⋙ G) E P).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f]
  exact CechCoefficientComposition.piComparison F G (fun i : (E.obj (op ⦋n⦌)).I => P.obj (op ((E.obj (op ⦋n⦌)).obj i)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CoefficientComposition.CechCoefficientComposition
