import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSourceNaturality

/-! # Total Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSquare.CechConeTotalConeSquare

noncomputable section

/-! A commuting square of actual cones induces its original Cech-total
augmentation square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C) {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} {M N : CochainComplex A ℕ}
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P) (θ : (Functor.const Cᵒᵖ).obj N ⟶ Q)
  (a : P ⟶ Q) (b : M ⟶ N) (h : η ≫ a = (Functor.const Cᵒᵖ).map b ≫ θ)

include h in
theorem natural : Total.CechConeTotal.augmentation U P M η ≫ (TotalFunctor.CechConeTotalFunctor.functor U).map a =
    b ≫ Total.CechConeTotal.augmentation U Q N θ :=
  (TotalFunctor.CechConeTotalFunctor.augmentation U M η a).trans
    ((congrArg (fun η' => Total.CechConeTotal.augmentation U Q M η') h).trans
      (TotalSourceNaturality.CechConeTotalSourceNaturality.augmentation U Q N M θ b).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSquare.CechConeTotalConeSquare
