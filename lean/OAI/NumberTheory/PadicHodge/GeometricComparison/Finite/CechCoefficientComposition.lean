import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange

/-! # Cech Coefficient Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientComposition.FiniteCechCoefficientComposition

noncomputable section

/-! The original finite Cech coefficient comparison respects composition
of additive coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z w' z' w'' z'' t
variable {A : Type w} [Category.{z} A] [Abelian A]
  {B : Type w'} [Category.{z'} B] [Abelian B]
  {D : Type w''} [Category.{z''} D] [Abelian D]
  [HasProducts.{t} A] [HasProducts.{t} B] [HasProducts.{t} D]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]

omit [F.Additive] [G.Additive] [Abelian A] [Abelian B] [Abelian D] in
theorem products {ι : Type t} (X : ι → A) :
    piComparison (F ⋙ G) X = G.map (piComparison F X) ≫ piComparison G (fun i => F.obj (X i)) := by
  apply Pi.hom_ext
  intro i
  rw [piComparison_comp_π]
  change G.map (F.map (Pi.π X i)) =
    (G.map (piComparison F X) ≫ piComparison G (fun j => F.obj (X j))) ≫
      Pi.π (fun j => G.obj (F.obj (X j))) i
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp, piComparison_comp_π]

variable {C : Type u} [Category.{v} C] (E : SimplicialObject (FormalCoproduct.{t} C))
  (hE : ∀ n : SimplexCategory, Finite (E.obj (op n)).I) (P : Cᵒᵖ ⥤ A)

theorem complexes : (CechCoefficientChange.FiniteCechCoefficientChange.complexIso (F ⋙ G) E hE P).hom =
    (G.mapHomologicalComplex (.up ℕ)).map (CechCoefficientChange.FiniteCechCoefficientChange.complexIso F E hE P).hom ≫
      (CechCoefficientChange.FiniteCechCoefficientChange.complexIso G E hE (P ⋙ F)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (CechCoefficientChange.FiniteCechCoefficientChange.complexIso (F ⋙ G) E hE P).hom.f n =
    G.map ((CechCoefficientChange.FiniteCechCoefficientChange.complexIso F E hE P).hom.f n) ≫
      (CechCoefficientChange.FiniteCechCoefficientChange.complexIso G E hE (P ⋙ F)).hom.f n
  rw [CechCoefficientChange.FiniteCechCoefficientChange.hom_f, CechCoefficientChange.FiniteCechCoefficientChange.hom_f, CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  exact products F G (fun i : (E.obj (op ⦋n⦌)).I => P.obj (op ((E.obj (op ⦋n⦌)).obj i)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientComposition.FiniteCechCoefficientComposition
