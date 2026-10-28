import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange

/-! # Cech Coefficient Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientTransformation.FiniteCechCoefficientTransformation

noncomputable section

/-! Finite Cech coefficient comparison is natural in a transformation
of additive coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z w' z' t
variable {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{t} A] [HasProducts.{t} B]
  (F G : A ⥤ B) [F.Additive] [G.Additive] (α : F ⟶ G)

omit [F.Additive] [G.Additive] [Abelian A] [Abelian B] in
theorem products {ι : Type t} (X : ι → A) :
    α.app (∏ᶜ X) ≫ piComparison G X = piComparison F X ≫ Limits.Pi.map (fun i => α.app (X i)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, piComparison_comp_π, Pi.map_π, piComparison_comp_π_assoc]
  exact (α.naturality (Pi.π X i)).symm

variable {C : Type u} [Category.{v} C] (E : SimplicialObject (FormalCoproduct.{t} C))
  (hE : ∀ n : SimplexCategory, Finite (E.obj (op n)).I) (P : Cᵒᵖ ⥤ A)

theorem complexes : (α.mapHomologicalComplex (.up ℕ)).app ((FormalCoproduct.cochainComplexFunctor E).obj P) ≫
    (CechCoefficientChange.FiniteCechCoefficientChange.complexIso G E hE P).hom =
      (CechCoefficientChange.FiniteCechCoefficientChange.complexIso F E hE P).hom ≫
        (FormalCoproduct.cochainComplexFunctor E).map (Functor.whiskerLeft P α) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  exact products F G α (fun i : (E.obj (op ⦋n⦌)).I => P.obj (op ((E.obj (op ⦋n⦌)).obj i)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientTransformation.FiniteCechCoefficientTransformation
