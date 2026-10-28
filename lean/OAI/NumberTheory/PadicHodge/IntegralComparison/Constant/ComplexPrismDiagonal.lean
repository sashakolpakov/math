import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismCone

/-! # Complex Prism Diagonal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismDiagonal.Cone

noncomputable section

/-! Own-chart evaluation of the prism cone is the original frame
map to the section diagonal. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Preadditive A]
  (Q : C ⥤ CochainComplex A ℕ) (P : C ⥤ CochainComplex (C ⥤ A) ℕ)
attribute [local instance] ComplexPrismCone.constZero
variable (a : Q ⋙ (Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ) ⟶ P)

theorem diagonal (V : C) : ((ComplexPrismCone.cone Q P a).app V).app V =
    (GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation Q P a).app V := by
  change _ = _ ≫ 𝟙 _
  exact (Category.comp_id _).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismDiagonal.Cone
