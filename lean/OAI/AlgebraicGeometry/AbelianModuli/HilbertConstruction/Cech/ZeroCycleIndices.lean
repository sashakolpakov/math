/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafZeroExact.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafAugmentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionSections

/-! # Zero Cycle Indices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleIndices.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

def cechConstIndex (i₀ : ι) : Fin 1 → ι := fun _ => i₀

def cechPairIndex (i₀ : ι) (i : Fin 1 → ι) : Fin 2 → ι := Fin.cases i₀ i

theorem cechSingletonIntersection_eq (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 => U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0)
  · exact leOfHom (Pi.lift fun k : Fin 1 => homOfLE (by
      rw [Subsingleton.elim k 0]))

theorem cechConstIntersection_eq {V : Opens X} (i₀ : ι) (hV : V ≤ U i₀) :
    V ⊓ (∏ᶜ fun k : Fin 1 => U (cechConstIndex i₀ k)) = V := by
  rw [cechSingletonIntersection_eq U (cechConstIndex i₀), inf_eq_left]
  exact hV

theorem cechPairDeleteZero (i₀ : ι) (i : Fin 1 → ι) :
    cechPairIndex i₀ i ∘
        (SimplexCategory.δ (0 : Fin 2)).toOrderHom = i := by
  funext k
  fin_cases k
  rfl

theorem cechPairDeleteOne (i₀ : ι) (i : Fin 1 → ι) :
    cechPairIndex i₀ i ∘
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom = cechConstIndex i₀ := by
  funext k
  fin_cases k
  rfl

theorem cechPairLEZero (i₀ : ι) (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 2 => U (cechPairIndex i₀ i k)) ≤
      ∏ᶜ fun k : Fin 1 => U (i k) := by
  rw [← congrArg (fun q : Fin 1 → ι =>
    ∏ᶜ fun k : Fin 1 => U (q k)) (cechPairDeleteZero i₀ i)]
  exact leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ (cechPairIndex i₀ i))

theorem cechPairLEOne (i₀ : ι) (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 2 => U (cechPairIndex i₀ i k)) ≤
      ∏ᶜ fun k : Fin 1 => U (cechConstIndex i₀ k) := by
  rw [← congrArg (fun q : Fin 1 → ι =>
    ∏ᶜ fun k : Fin 1 => U (q k)) (cechPairDeleteOne i₀ i)]
  exact leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ (cechPairIndex i₀ i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ZeroCycleIndices.IntrinsicCech
