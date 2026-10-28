import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient

/-! # Total Coefficient Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation

noncomputable section

/-! The finite Čech coefficient comparison carries the original natural
augmentation to the augmentation of the mapped cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z w' z' t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{t} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{t} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type t} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (M : CochainComplex A ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

local notation "G" => F.mapHomologicalComplex (ComplexShape.up ℕ)

def mappedCone : (Functor.const Cᵒᵖ).obj ((G).obj M) ⟶ TotalCoefficient.CechConeTotalCoefficient.mapped F P :=
  (Functor.constComp Cᵒᵖ M G).inv ≫ Functor.whiskerRight η G

omit [HasBinaryProducts C] [HasProducts.{t} A] [HasCoproducts.{0} A]
  [HasProducts.{t} B] [HasCoproducts.{0} B] in
theorem mappedCone_app (V : Cᵒᵖ) : (mappedCone F P M η).app V = (G).map (η.app V) :=
  Category.id_comp _

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem zeroMap : (G).map (Total.CechConeTotal.zeroMap U P M η) ≫
    (TotalCoefficient.CechConeTotalCoefficient.horizontalIso F U P).hom.f 0 =
  Total.CechConeTotal.zeroMap U (TotalCoefficient.CechConeTotalCoefficient.mapped F P) ((G).obj M) (mappedCone F P M η) := by
  change (G).map (Total.CechConeTotal.zeroMap U P M η) ≫
      (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (IntegralComparison.NonemptyCechNerve.nerve U)
        (TotalCoefficient.CechConeTotalCoefficient.finite_indices U) P).hom.f 0 = _
  rw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  change (G).map (Pi.lift (fun i : Fin 1 → ι => η.app (op (∏ᶜ (U ∘ i))))) ≫
      piComparison G (fun i : Fin 1 → ι => P.obj (op (∏ᶜ (U ∘ i)))) =
    Pi.lift (fun i : Fin 1 → ι => (mappedCone F P M η).app (op (∏ᶜ (U ∘ i))))
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, piComparison_comp_π, ← CategoryTheory.Functor.map_comp, Pi.lift_comp_π]
  erw [Pi.lift_comp_π, mappedCone_app]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation
