import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Total Section Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSectionMap.CechConeTotalSectionMap

noncomputable section

/-! The canonical Cech total functor-square map has the actual
section-pullback formula, before specializing the geometric diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z' w'' z''
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {D : Type w''} [Category.{z''} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (T : A ⥤ B) [T.Additive] (S : A ⥤ D) [S.Additive] (S' : B ⥤ D) [S'.Additive]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S')

omit [HasProducts.{0} D] [HasCoproducts.{0} D] in
theorem map_eq : TotalFunctorSquare.CechConeTotalFunctorSquare.map T S S' U P Q a b =
    Section.CochainPullback.SectionCochainPullback.map T S S' b (TotalLevelMap.CechConeTotalLevelMap.map T U P Q a) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSectionMap.CechConeTotalSectionMap
