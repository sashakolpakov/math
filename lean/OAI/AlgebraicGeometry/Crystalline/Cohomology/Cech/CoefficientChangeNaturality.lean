import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Coefficient Change Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality

noncomputable section

/-! # Naturality of the canonical coefficient-change isomorphism for Čech complexes -/

open _root_.CategoryTheory Limits Opposite Simplicial

universe w v vA vB u uA uB

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)

theorem piComparison_map {α : Type w} {X Y : α → A} (f : ∀ i, X i ⟶ Y i) :
    G.map (Limits.Pi.map f) ≫ piComparison G Y =
      piComparison G X ≫ Limits.Pi.map (fun i => G.map (f i)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, piComparison_comp_π, Pi.map_π]
  rw [← G.map_comp, Pi.map_π, G.map_comp, piComparison_comp_π_assoc]

variable {C : Type u} [Category.{v} C]
  (E : SimplicialObject (FormalCoproduct.{w} C))
  [PreservesLimitsOfSize.{w, w} G] [Preadditive A] [Preadditive B] [G.Additive]

theorem hom_f (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (CoefficientChange.CechCoefficientChange.complexIso G E P).hom.f n =
      piComparison G (fun i : (E.obj (op ⦋n⦌)).I => P.obj (op ((E.obj (op ⦋n⦌)).obj i))) :=
  Category.id_comp _

theorem naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((FormalCoproduct.cochainComplexFunctor E).map f) ≫
      (CoefficientChange.CechCoefficientChange.complexIso G E Q).hom =
    (CoefficientChange.CechCoefficientChange.complexIso G E P).hom ≫
      (FormalCoproduct.cochainComplexFunctor E).map (Functor.whiskerRight f G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, hom_f]
  exact piComparison_map G (fun i : (E.obj (op ⦋n⦌)).I =>
    f.app (op ((E.obj (op ⦋n⦌)).obj i)))

def iso : FormalCoproduct.cochainComplexFunctor E ⋙
    G.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (Functor.whiskeringRight Cᵒᵖ A B).obj G ⋙ FormalCoproduct.cochainComplexFunctor E :=
  NatIso.ofComponents (fun P => CoefficientChange.CechCoefficientChange.complexIso G E P)
    (by intro P Q f; exact naturality G E f)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality
