import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits

/-! # Nonempty Cech Additive -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechAdditive.NonemptyCechFunctorAdditive

noncomputable section

/-! The nonempty Cech cochain functor is additive in the coefficient presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {ι : Type w} (U : ι → C)
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{w} A]

instance additive : (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U)).Additive
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechAdditive.NonemptyCechFunctorAdditive
