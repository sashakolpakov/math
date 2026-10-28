import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.ChartTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalAugmentationNaturality

/-! # Mapped Chart Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartTotal.SemilatticeMappedChartTotal

noncomputable section

/-! The canonical local chart cone maps to the original global total
after coefficient restriction and preserves every original augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z t
variable (C : Type u) [SemilatticeInf C] {ι : Type} [Finite ι]
  (U : ι → C) (I : C)
  {A : Type v} [Category.{w} A] [Abelian A]
  [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type z} [Category.{t} B] [Abelian B]
  [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ V : C, IsIso
    ((F.mapHomologicalComplex (.up ℕ)).map
      (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op)))

local notation "G" => F.mapHomologicalComplex (ComplexShape.up ℕ)
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped F P

def map : (G).obj (P.obj (op I)) ⟶ (G).obj (CechCone.Total.CechConeTotal.total U P) :=
  ChartTotal.SemilatticeChartTotal.map C U I Q h ≫ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).inv

theorem factorization (M : CochainComplex A ℕ)
    (η : (Functor.const Cᵒᵖ).obj M ⟶ P) :
    (G).map (η.app (op I)) ≫ SemilatticeMappedChartTotal.map C U I F P h =
      (G).map (CechCone.Total.CechConeTotal.augmentation U P M η) := by
  let θ := CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone F P M η
  have hf := ChartTotal.SemilatticeChartTotal.factorization C U I Q h ((G).obj M) θ
  rw [CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app] at hf
  have ht := CechCone.TotalAugmentationNaturality.CechConeTotalAugmentationNaturality.augmentation F U P M η
  dsimp only [SemilatticeMappedChartTotal.map]
  rw [← Category.assoc, ← hf, ← ht, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem comparison (M : CochainComplex A ℕ)
    (η : (Functor.const Cᵒᵖ).obj M ⟶ P) {K : CochainComplex A ℕ}
    (b : CechCone.Total.CechConeTotal.total U P ⟶ K) :
    (G).map (η.app (op I)) ≫
        (SemilatticeMappedChartTotal.map C U I F P h ≫ (G).map b) =
      (G).map (CechCone.Total.CechConeTotal.augmentation U P M η ≫ b) := by
  rw [← Category.assoc, factorization, CategoryTheory.Functor.map_comp]

theorem factorization_through_iso (M : CochainComplex A ℕ)
    (η : (Functor.const Cᵒᵖ).obj M ⟶ P) {K : CochainComplex A ℕ}
    (e : K ≅ CechCone.Total.CechConeTotal.total U P) (a : M ⟶ K)
    (ha : a ≫ e.hom = CechCone.Total.CechConeTotal.augmentation U P M η) :
    (G).map (η.app (op I)) ≫
        (SemilatticeMappedChartTotal.map C U I F P h ≫ (G).map e.inv) = (G).map a := by
  rw [comparison, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartTotal.SemilatticeMappedChartTotal
