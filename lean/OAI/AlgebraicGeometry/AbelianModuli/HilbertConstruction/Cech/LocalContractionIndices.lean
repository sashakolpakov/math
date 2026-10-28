/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechSheafLocalContraction.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafComplex

/-! # Local Contraction Indices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionIndices.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X)
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

def cechPrependIndex {n : ℕ} (i₀ : ι) (i : Fin (n + 1) → ι) :
    Fin (n + 2) → ι :=
  Fin.cases i₀ i

theorem cechPrependDeleteZero {n : ℕ} (i₀ : ι) (i : Fin (n + 1) → ι) :
    cechPrependIndex i₀ i ∘
        (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom = i := by
  funext k
  rfl

theorem cechPrependDeleteSucc {n : ℕ} (i₀ : ι) (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    cechPrependIndex i₀ i ∘
        (SimplexCategory.δ k.succ).toOrderHom =
      cechPrependIndex i₀
        (i ∘ (SimplexCategory.δ k).toOrderHom) := by
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · simp [cechPrependIndex, SimplexCategory.δ, Function.comp_apply]

theorem cechPrependIntersection_eq {n : ℕ} {V : Opens X} (i₀ : ι)
    (hV : V ≤ U i₀) (i : Fin (n + 1) → ι) :
    V ⊓ (∏ᶜ fun k : Fin (n + 2) => U (cechPrependIndex i₀ i k)) =
      V ⊓ (∏ᶜ fun k : Fin (n + 1) => U (i k)) := by
  apply le_antisymm
  · refine le_inf inf_le_left (leOfHom (Pi.lift fun k => ?_))
    exact homOfLE (inf_le_right.trans
      (leOfHom (Pi.π (fun k : Fin (n + 2) => U (cechPrependIndex i₀ i k)) k.succ)))
  · refine le_inf inf_le_left (leOfHom (Pi.lift fun k => ?_))
    refine Fin.cases ?_ (fun j => ?_) k
    · exact homOfLE (inf_le_left.trans hV)
    · exact homOfLE (inf_le_right.trans
        (leOfHom (Pi.π (fun j : Fin (n + 1) => U (i j)) j)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.LocalContractionIndices.IntrinsicCech
