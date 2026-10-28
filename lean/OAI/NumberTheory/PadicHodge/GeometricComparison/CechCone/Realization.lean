import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientComposition

/-! # Realization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Realization.CechConeRealization

noncomputable section

/-! A cone in a coefficient category gives a map to the original
finite Čech total. This map commutes with further coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z x y a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type x} [Category.{y} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (M : CochainComplex B ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ TotalCoefficient.CechConeTotalCoefficient.mapped F P)

def map : M ⟶ (F.mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total U P) :=
  Total.CechConeTotal.augmentation U (TotalCoefficient.CechConeTotalCoefficient.mapped F P) M η ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).inv

variable {D : Type a} [Category.{b} D] [Abelian D]
  [HasProducts.{0} D] [HasCoproducts.{0} D] (G : B ⥤ D) [G.Additive]

theorem coefficients : (G.mapHomologicalComplex (.up ℕ)).map (CechConeRealization.map F U P M η) =
    CechConeRealization.map (F ⋙ G) U P ((G.mapHomologicalComplex (.up ℕ)).obj M)
      (TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone G
        (TotalCoefficient.CechConeTotalCoefficient.mapped F P) M η) := by
  let Q := TotalCoefficient.CechConeTotalCoefficient.mapped F P
  let θ := TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone G Q M η
  have ha := TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation G U Q M η
  have haug : (G.mapHomologicalComplex (.up ℕ)).map (Total.CechConeTotal.augmentation U Q M η) =
      Total.CechConeTotal.augmentation U (TotalCoefficient.CechConeTotalCoefficient.mapped G Q)
        ((G.mapHomologicalComplex (.up ℕ)).obj M) θ ≫
          (TotalCoefficient.CechConeTotalCoefficient.totalIso G U Q).inv :=
    (TotalCoefficient.CechConeTotalCoefficient.totalIso G U Q).eq_comp_inv.mpr ha
  have he : TotalCoefficient.CechConeTotalCoefficient.totalIso (F ⋙ G) U P =
      (G.mapHomologicalComplex (.up ℕ)).mapIso (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P) ≪≫
        TotalCoefficient.CechConeTotalCoefficient.totalIso G U Q :=
    Iso.ext (CoefficientComposition.CechConeCoefficientComposition.total F G U P)
  have hi := congrArg Iso.inv he
  change (G.mapHomologicalComplex (.up ℕ)).map
      (Total.CechConeTotal.augmentation U Q M η ≫ (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).inv) =
    Total.CechConeTotal.augmentation U (TotalCoefficient.CechConeTotalCoefficient.mapped G Q)
      ((G.mapHomologicalComplex (.up ℕ)).obj M) θ ≫
        (TotalCoefficient.CechConeTotalCoefficient.totalIso (F ⋙ G) U P).inv
  rw [CategoryTheory.Functor.map_comp, haug, hi]
  exact Category.assoc _ _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Realization.CechConeRealization
